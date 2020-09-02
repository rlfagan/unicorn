
#line 1 "ext/unicorn_http/unicorn_http.rl"
/**
 * Copyright (c) 2009 Eric Wong (all bugs are Eric's fault)
 * Copyright (c) 2005 Zed A. Shaw
 * You can redistribute it and/or modify it under the same terms as Ruby 1.8 or
 * the GPLv2+ (GPLv3+ preferred)
 */
#include "ruby.h"
#include "ext_help.h"
#include <assert.h>
#include <string.h>
#include <sys/types.h>
#include "common_field_optimization.h"
#include "global_variables.h"
#include "c_util.h"

void init_unicorn_httpdate(void);

#define UH_FL_CHUNKED  0x1
#define UH_FL_HASBODY  0x2
#define UH_FL_INBODY   0x4
#define UH_FL_HASTRAILER 0x8
#define UH_FL_INTRAILER 0x10
#define UH_FL_INCHUNK  0x20
#define UH_FL_REQEOF 0x40
#define UH_FL_KAVERSION 0x80
#define UH_FL_HASHEADER 0x100
#define UH_FL_TO_CLEAR 0x200
#define UH_FL_RESSTART 0x400 /* for check_client_connection */
#define UH_FL_HIJACK 0x800

/* all of these flags need to be set for keepalive to be supported */
#define UH_FL_KEEPALIVE (UH_FL_KAVERSION | UH_FL_REQEOF | UH_FL_HASHEADER)

static unsigned int MAX_HEADER_LEN = 1024 * (80 + 32); /* same as Mongrel */

/* this is only intended for use with Rainbows! */
static VALUE set_maxhdrlen(VALUE self, VALUE len)
{
  return UINT2NUM(MAX_HEADER_LEN = NUM2UINT(len));
}

/* keep this small for other servers (e.g. yahns) since every client has one */
struct http_parser {
  int cs; /* Ragel internal state */
  unsigned int flags;
  unsigned int mark;
  unsigned int offset;
  union { /* these 2 fields don't nest */
    unsigned int field;
    unsigned int query;
  } start;
  union {
    unsigned int field_len; /* only used during header processing */
    unsigned int dest_offset; /* only used during body processing */
  } s;
  VALUE buf;
  VALUE env;
  VALUE cont; /* Qfalse: unset, Qnil: ignored header, T_STRING: append */
  union {
    off_t content;
    off_t chunk;
  } len;
};

static ID id_set_backtrace, id_is_chunked_p;
static VALUE cHttpParser;

#ifdef HAVE_RB_HASH_CLEAR /* Ruby >= 2.0 */
#  define my_hash_clear(h) (void)rb_hash_clear(h)
#else /* !HAVE_RB_HASH_CLEAR - Ruby <= 1.9.3 */

static ID id_clear;

static void my_hash_clear(VALUE h)
{
  rb_funcall(h, id_clear, 0);
}
#endif /* HAVE_RB_HASH_CLEAR */

static void finalize_header(struct http_parser *hp);

static void parser_raise(VALUE klass, const char *msg)
{
  VALUE exc = rb_exc_new2(klass, msg);
  VALUE bt = rb_ary_new();

  rb_funcall(exc, id_set_backtrace, 1, bt);
  rb_exc_raise(exc);
}

static inline unsigned int ulong2uint(unsigned long n)
{
  unsigned int i = (unsigned int)n;

  if (sizeof(unsigned int) != sizeof(unsigned long)) {
    if ((unsigned long)i != n) {
      rb_raise(rb_eRangeError, "too large to be 32-bit uint: %lu", n);
    }
  }
  return i;
}

#define REMAINING (unsigned long)(pe - p)
#define LEN(AT, FPC) (ulong2uint(FPC - buffer) - hp->AT)
#define MARK(M,FPC) (hp->M = ulong2uint((FPC) - buffer))
#define PTR_TO(F) (buffer + hp->F)
#define STR_NEW(M,FPC) rb_str_new(PTR_TO(M), LEN(M, FPC))
#define STRIPPED_STR_NEW(M,FPC) stripped_str_new(PTR_TO(M), LEN(M, FPC))

#define HP_FL_TEST(hp,fl) ((hp)->flags & (UH_FL_##fl))
#define HP_FL_SET(hp,fl) ((hp)->flags |= (UH_FL_##fl))
#define HP_FL_UNSET(hp,fl) ((hp)->flags &= ~(UH_FL_##fl))
#define HP_FL_ALL(hp,fl) (HP_FL_TEST(hp, fl) == (UH_FL_##fl))

static int is_lws(char c)
{
  return (c == ' ' || c == '\t');
}

static VALUE stripped_str_new(const char *str, long len)
{
  long end;

  for (end = len - 1; end >= 0 && is_lws(str[end]); end--);

  return rb_str_new(str, end + 1);
}

/*
 * handles values of the "Connection:" header, keepalive is implied
 * for HTTP/1.1 but needs to be explicitly enabled with HTTP/1.0
 * Additionally, we require GET/HEAD requests to support keepalive.
 */
static void hp_keepalive_connection(struct http_parser *hp, VALUE val)
{
  if (STR_CSTR_CASE_EQ(val, "keep-alive")) {
    /* basically have HTTP/1.0 masquerade as HTTP/1.1+ */
    HP_FL_SET(hp, KAVERSION);
  } else if (STR_CSTR_CASE_EQ(val, "close")) {
    /*
     * it doesn't matter what HTTP version or request method we have,
     * if a client says "Connection: close", we disable keepalive
     */
    HP_FL_UNSET(hp, KAVERSION);
  } else {
    /*
     * client could've sent anything, ignore it for now.  Maybe
     * "HP_FL_UNSET(hp, KAVERSION);" just in case?
     * Raising an exception might be too mean...
     */
  }
}

static void
request_method(struct http_parser *hp, const char *ptr, size_t len)
{
  VALUE v = rb_str_new(ptr, len);

  rb_hash_aset(hp->env, g_request_method, v);
}

static void
http_version(struct http_parser *hp, const char *ptr, size_t len)
{
  VALUE v;

  HP_FL_SET(hp, HASHEADER);

  if (CONST_MEM_EQ("HTTP/1.1", ptr, len)) {
    /* HTTP/1.1 implies keepalive unless "Connection: close" is set */
    HP_FL_SET(hp, KAVERSION);
    v = g_http_11;
  } else if (CONST_MEM_EQ("HTTP/1.0", ptr, len)) {
    v = g_http_10;
  } else {
    v = rb_str_new(ptr, len);
  }
  rb_hash_aset(hp->env, g_server_protocol, v);
  rb_hash_aset(hp->env, g_http_version, v);
}

static inline void hp_invalid_if_trailer(struct http_parser *hp)
{
  if (HP_FL_TEST(hp, INTRAILER))
    parser_raise(eHttpParserError, "invalid Trailer");
}

static void write_cont_value(struct http_parser *hp,
                             char *buffer, const char *p)
{
  char *vptr;
  long end;
  long len = LEN(mark, p);
  long cont_len;

  if (hp->cont == Qfalse)
     parser_raise(eHttpParserError, "invalid continuation line");
  if (NIL_P(hp->cont))
     return; /* we're ignoring this header (probably Host:) */

  assert(TYPE(hp->cont) == T_STRING && "continuation line is not a string");
  assert(hp->mark > 0 && "impossible continuation line offset");

  if (len == 0)
    return;

  cont_len = RSTRING_LEN(hp->cont);
  if (cont_len > 0) {
    --hp->mark;
    len = LEN(mark, p);
  }
  vptr = PTR_TO(mark);

  /* normalize tab to space */
  if (cont_len > 0) {
    assert((' ' == *vptr || '\t' == *vptr) && "invalid leading white space");
    *vptr = ' ';
  }

  for (end = len - 1; end >= 0 && is_lws(vptr[end]); end--);
  rb_str_buf_cat(hp->cont, vptr, end + 1);
}

static int is_chunked(VALUE v)
{
  /* common case first */
  if (STR_CSTR_CASE_EQ(v, "chunked"))
    return 1;

  /*
   * call Ruby function in unicorn/http_request.rb to deal with unlikely
   * comma-delimited case
   */
  return rb_funcall(cHttpParser, id_is_chunked_p, 1, v) != Qfalse;
}

static void write_value(struct http_parser *hp,
                        const char *buffer, const char *p)
{
  VALUE f = find_common_field(PTR_TO(start.field), hp->s.field_len);
  VALUE v;
  VALUE e;

  VALIDATE_MAX_LENGTH(LEN(mark, p), FIELD_VALUE);
  v = LEN(mark, p) == 0 ? rb_str_buf_new(128) : STRIPPED_STR_NEW(mark, p);
  if (NIL_P(f)) {
    const char *field = PTR_TO(start.field);
    size_t flen = hp->s.field_len;

    VALIDATE_MAX_LENGTH(flen, FIELD_NAME);

    /*
     * ignore "Version" headers since they conflict with the HTTP_VERSION
     * rack env variable.
     */
    if (CONST_MEM_EQ("VERSION", field, flen)) {
      hp->cont = Qnil;
      return;
    }
    f = uncommon_field(field, flen);
  } else if (f == g_http_connection) {
    hp_keepalive_connection(hp, v);
  } else if (f == g_content_length && !HP_FL_TEST(hp, CHUNKED)) {
    if (hp->len.content)
      parser_raise(eHttpParserError, "Content-Length already set");
    hp->len.content = parse_length(RSTRING_PTR(v), RSTRING_LEN(v));
    if (hp->len.content < 0)
      parser_raise(eHttpParserError, "invalid Content-Length");
    if (hp->len.content != 0)
      HP_FL_SET(hp, HASBODY);
    hp_invalid_if_trailer(hp);
  } else if (f == g_http_transfer_encoding) {
    if (is_chunked(v)) {
      if (HP_FL_TEST(hp, CHUNKED))
        /*
         * RFC 7230 3.3.1:
         * A sender MUST NOT apply chunked more than once to a message body
         * (i.e., chunking an already chunked message is not allowed).
         */
        parser_raise(eHttpParserError, "Transfer-Encoding double chunked");

      HP_FL_SET(hp, CHUNKED);
      HP_FL_SET(hp, HASBODY);

      /* RFC 7230 3.3.3, 3: favor chunked if Content-Length exists */
      hp->len.content = 0;
    } else if (HP_FL_TEST(hp, CHUNKED)) {
      /*
       * RFC 7230 3.3.3, point 3 states:
       * If a Transfer-Encoding header field is present in a request and
       * the chunked transfer coding is not the final encoding, the
       * message body length cannot be determined reliably; the server
       * MUST respond with the 400 (Bad Request) status code and then
       * close the connection.
       */
      parser_raise(eHttpParserError, "invalid Transfer-Encoding");
    }
    hp_invalid_if_trailer(hp);
  } else if (f == g_http_trailer) {
    HP_FL_SET(hp, HASTRAILER);
    hp_invalid_if_trailer(hp);
  } else {
    assert(TYPE(f) == T_STRING && "memoized object is not a string");
    assert_frozen(f);
  }

  e = rb_hash_aref(hp->env, f);
  if (NIL_P(e)) {
    hp->cont = rb_hash_aset(hp->env, f, v);
  } else if (f == g_http_host) {
    /*
     * ignored, absolute URLs in REQUEST_URI take precedence over
     * the Host: header (ref: rfc 2616, section 5.2.1)
     */
     hp->cont = Qnil;
  } else {
    rb_str_buf_cat(e, ",", 1);
    hp->cont = rb_str_buf_append(e, v);
  }
}

/** Machine **/


#line 431 "ext/unicorn_http/unicorn_http.rl"


/** Data **/

#line 333 "ext/unicorn_http/unicorn_http.c"
static const char _http_parser_actions[] = {
	0, 1, 0, 1, 2, 1, 3, 1, 
	4, 1, 5, 1, 6, 1, 7, 1, 
	8, 1, 9, 1, 11, 1, 12, 1, 
	13, 1, 15, 1, 16, 1, 17, 1, 
	18, 1, 19, 1, 20, 1, 21, 2, 
	0, 3, 2, 0, 12, 2, 1, 2, 
	2, 5, 6, 2, 5, 7, 2, 10, 
	0, 2, 11, 18, 2, 12, 18, 2, 
	14, 11, 2, 16, 11, 3, 0, 12, 
	18, 3, 13, 14, 11, 3, 14, 11, 
	18, 3, 16, 11, 18, 4, 13, 14, 
	11, 18
};

static const short _http_parser_key_offsets[] = {
	0, 0, 16, 32, 36, 38, 39, 40, 
	41, 42, 43, 45, 48, 50, 54, 73, 
	80, 87, 88, 89, 105, 112, 119, 125, 
	131, 137, 143, 150, 156, 162, 168, 174, 
	180, 186, 188, 190, 192, 195, 196, 197, 
	215, 226, 232, 238, 257, 270, 287, 305, 
	317, 318, 334, 350, 366, 382, 398, 414, 
	430, 446, 462, 478, 494, 510, 526, 542, 
	558, 574, 590, 606, 607, 624, 641, 657, 
	661, 665, 673, 681, 687, 693, 702, 708, 
	714, 722, 730, 736, 742, 744, 746, 748, 
	751, 752, 753, 771, 782, 788, 794, 813, 
	826, 843, 861, 873, 874, 881, 891, 892, 
	901, 901, 903, 904, 905, 925, 944, 962, 
	982, 1001, 1019, 1038, 1045, 1052, 1053, 1054, 
	1070, 1077, 1084, 1084, 1084
};

static const char _http_parser_trans_keys[] = {
	33, 71, 124, 126, 35, 39, 42, 43, 
	45, 46, 48, 57, 65, 90, 94, 122, 
	32, 33, 124, 126, 35, 39, 42, 43, 
	45, 46, 48, 57, 65, 90, 94, 122, 
	42, 47, 72, 104, 32, 35, 72, 84, 
	84, 80, 47, 48, 57, 46, 48, 57, 
	48, 57, 10, 13, 48, 57, 9, 10, 
	13, 32, 33, 124, 126, 35, 39, 42, 
	43, 45, 46, 48, 57, 65, 90, 94, 
	122, 9, 10, 13, 32, 127, 0, 31, 
	10, 13, 127, 0, 8, 11, 31, 10, 
	10, 33, 58, 124, 126, 35, 39, 42, 
	43, 45, 46, 48, 57, 65, 90, 94, 
	122, 9, 10, 13, 32, 127, 0, 31, 
	10, 13, 127, 0, 8, 11, 31, 32, 
	35, 37, 127, 0, 31, 32, 35, 37, 
	127, 0, 31, 48, 57, 65, 70, 97, 
	102, 48, 57, 65, 70, 97, 102, 32, 
	35, 37, 63, 127, 0, 31, 48, 57, 
	65, 70, 97, 102, 48, 57, 65, 70, 
	97, 102, 32, 35, 37, 127, 0, 31, 
	32, 35, 37, 127, 0, 31, 48, 57, 
	65, 70, 97, 102, 48, 57, 65, 70, 
	97, 102, 84, 116, 84, 116, 80, 112, 
	58, 83, 115, 47, 47, 37, 47, 60, 
	91, 95, 127, 0, 32, 34, 35, 45, 
	57, 62, 64, 65, 90, 97, 122, 37, 
	47, 60, 64, 127, 0, 32, 34, 35, 
	62, 63, 48, 57, 65, 70, 97, 102, 
	48, 57, 65, 70, 97, 102, 37, 47, 
	58, 60, 64, 95, 127, 0, 32, 34, 
	35, 45, 57, 62, 63, 65, 90, 97, 
	122, 37, 47, 60, 64, 127, 0, 32, 
	34, 35, 48, 57, 62, 63, 37, 47, 
	60, 64, 127, 0, 32, 34, 35, 48, 
	58, 62, 63, 65, 70, 97, 102, 37, 
	47, 60, 64, 93, 127, 0, 32, 34, 
	35, 48, 58, 62, 63, 65, 70, 97, 
	102, 37, 47, 58, 60, 64, 127, 0, 
	32, 34, 35, 62, 63, 58, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 32, 32, 
	33, 69, 124, 126, 35, 39, 42, 43, 
	45, 46, 48, 57, 65, 90, 94, 122, 
	32, 33, 84, 124, 126, 35, 39, 42, 
	43, 45, 46, 48, 57, 65, 90, 94, 
	122, 32, 33, 124, 126, 35, 39, 42, 
	43, 45, 46, 48, 57, 65, 90, 94, 
	122, 42, 47, 72, 104, 10, 13, 32, 
	35, 10, 13, 32, 35, 37, 127, 0, 
	31, 10, 13, 32, 35, 37, 127, 0, 
	31, 48, 57, 65, 70, 97, 102, 48, 
	57, 65, 70, 97, 102, 10, 13, 32, 
	35, 37, 63, 127, 0, 31, 48, 57, 
	65, 70, 97, 102, 48, 57, 65, 70, 
	97, 102, 10, 13, 32, 35, 37, 127, 
	0, 31, 10, 13, 32, 35, 37, 127, 
	0, 31, 48, 57, 65, 70, 97, 102, 
	48, 57, 65, 70, 97, 102, 84, 116, 
	84, 116, 80, 112, 58, 83, 115, 47, 
	47, 37, 47, 60, 91, 95, 127, 0, 
	32, 34, 35, 45, 57, 62, 64, 65, 
	90, 97, 122, 37, 47, 60, 64, 127, 
	0, 32, 34, 35, 62, 63, 48, 57, 
	65, 70, 97, 102, 48, 57, 65, 70, 
	97, 102, 37, 47, 58, 60, 64, 95, 
	127, 0, 32, 34, 35, 45, 57, 62, 
	63, 65, 90, 97, 122, 37, 47, 60, 
	64, 127, 0, 32, 34, 35, 48, 57, 
	62, 63, 37, 47, 60, 64, 127, 0, 
	32, 34, 35, 48, 58, 62, 63, 65, 
	70, 97, 102, 37, 47, 60, 64, 93, 
	127, 0, 32, 34, 35, 48, 58, 62, 
	63, 65, 70, 97, 102, 37, 47, 58, 
	60, 64, 127, 0, 32, 34, 35, 62, 
	63, 58, 48, 49, 57, 65, 70, 97, 
	102, 10, 13, 48, 59, 49, 57, 65, 
	70, 97, 102, 10, 10, 13, 59, 48, 
	57, 65, 70, 97, 102, 10, 13, 10, 
	10, 10, 13, 32, 33, 59, 61, 124, 
	126, 35, 39, 42, 43, 45, 46, 48, 
	57, 65, 90, 94, 122, 10, 13, 33, 
	59, 61, 124, 126, 35, 39, 42, 43, 
	45, 46, 48, 57, 65, 90, 94, 122, 
	10, 13, 33, 59, 124, 126, 35, 39, 
	42, 43, 45, 46, 48, 57, 65, 90, 
	94, 122, 10, 13, 32, 33, 59, 61, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 10, 13, 
	33, 59, 61, 124, 126, 35, 39, 42, 
	43, 45, 46, 48, 57, 65, 90, 94, 
	122, 10, 13, 33, 59, 124, 126, 35, 
	39, 42, 43, 45, 46, 48, 57, 65, 
	90, 94, 122, 9, 10, 13, 32, 33, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 9, 10, 
	13, 32, 127, 0, 31, 10, 13, 127, 
	0, 8, 11, 31, 10, 10, 33, 58, 
	124, 126, 35, 39, 42, 43, 45, 46, 
	48, 57, 65, 90, 94, 122, 9, 10, 
	13, 32, 127, 0, 31, 10, 13, 127, 
	0, 8, 11, 31, 0
};

static const char _http_parser_single_lengths[] = {
	0, 4, 4, 4, 2, 1, 1, 1, 
	1, 1, 0, 1, 0, 2, 7, 5, 
	3, 1, 1, 4, 5, 3, 4, 4, 
	0, 0, 5, 0, 0, 4, 4, 0, 
	0, 2, 2, 2, 3, 1, 1, 6, 
	5, 0, 0, 7, 5, 5, 6, 6, 
	1, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 1, 5, 5, 4, 4, 
	4, 6, 6, 0, 0, 7, 0, 0, 
	6, 6, 0, 0, 2, 2, 2, 3, 
	1, 1, 6, 5, 0, 0, 7, 5, 
	5, 6, 6, 1, 1, 4, 1, 3, 
	0, 2, 1, 1, 8, 7, 6, 8, 
	7, 6, 7, 5, 3, 1, 1, 4, 
	5, 3, 0, 0, 0
};

static const char _http_parser_range_lengths[] = {
	0, 6, 6, 0, 0, 0, 0, 0, 
	0, 0, 1, 1, 1, 1, 6, 1, 
	2, 0, 0, 6, 1, 2, 1, 1, 
	3, 3, 1, 3, 3, 1, 1, 3, 
	3, 0, 0, 0, 0, 0, 0, 6, 
	3, 3, 3, 6, 4, 6, 6, 3, 
	0, 6, 6, 6, 6, 6, 6, 6, 
	6, 6, 6, 6, 6, 6, 6, 6, 
	6, 6, 6, 0, 6, 6, 6, 0, 
	0, 1, 1, 3, 3, 1, 3, 3, 
	1, 1, 3, 3, 0, 0, 0, 0, 
	0, 0, 6, 3, 3, 3, 6, 4, 
	6, 6, 3, 0, 3, 3, 0, 3, 
	0, 0, 0, 0, 6, 6, 6, 6, 
	6, 6, 6, 1, 2, 0, 0, 6, 
	1, 2, 0, 0, 0
};

static const short _http_parser_index_offsets[] = {
	0, 0, 11, 22, 27, 30, 32, 34, 
	36, 38, 40, 42, 45, 47, 51, 65, 
	72, 78, 80, 82, 93, 100, 106, 112, 
	118, 122, 126, 133, 137, 141, 147, 153, 
	157, 161, 164, 167, 170, 174, 176, 178, 
	191, 200, 204, 208, 222, 232, 244, 257, 
	267, 269, 280, 291, 302, 313, 324, 335, 
	346, 357, 368, 379, 390, 401, 412, 423, 
	434, 445, 456, 467, 469, 481, 493, 504, 
	509, 514, 522, 530, 534, 538, 547, 551, 
	555, 563, 571, 575, 579, 582, 585, 588, 
	592, 594, 596, 609, 618, 622, 626, 640, 
	650, 662, 675, 685, 687, 692, 700, 702, 
	709, 710, 713, 715, 717, 732, 746, 759, 
	774, 788, 801, 815, 822, 828, 830, 832, 
	843, 850, 856, 857, 858
};

static const unsigned char _http_parser_indicies[] = {
	0, 2, 0, 0, 0, 0, 0, 0, 
	0, 0, 1, 3, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 1, 5, 6, 
	7, 7, 1, 8, 9, 1, 10, 1, 
	11, 1, 12, 1, 13, 1, 14, 1, 
	15, 1, 16, 15, 1, 17, 1, 18, 
	19, 17, 1, 20, 21, 22, 20, 23, 
	23, 23, 23, 23, 23, 23, 23, 23, 
	1, 25, 26, 27, 25, 1, 1, 24, 
	29, 30, 1, 1, 1, 28, 31, 1, 
	21, 1, 32, 33, 32, 32, 32, 32, 
	32, 32, 32, 32, 1, 35, 36, 37, 
	35, 1, 1, 34, 39, 40, 1, 1, 
	1, 38, 42, 1, 43, 1, 1, 41, 
	45, 1, 46, 1, 1, 44, 47, 47, 
	47, 1, 44, 44, 44, 1, 49, 50, 
	51, 52, 1, 1, 48, 53, 53, 53, 
	1, 48, 48, 48, 1, 55, 56, 57, 
	1, 1, 54, 59, 60, 61, 1, 1, 
	58, 62, 62, 62, 1, 58, 58, 58, 
	1, 63, 63, 1, 64, 64, 1, 65, 
	65, 1, 66, 67, 67, 1, 68, 1, 
	69, 1, 71, 1, 1, 73, 72, 1, 
	1, 1, 72, 1, 72, 72, 70, 71, 
	1, 1, 69, 1, 1, 1, 1, 70, 
	74, 74, 74, 1, 70, 70, 70, 1, 
	71, 76, 77, 1, 69, 75, 1, 1, 
	1, 75, 1, 75, 75, 70, 71, 76, 
	1, 69, 1, 1, 1, 77, 1, 70, 
	71, 1, 1, 69, 1, 1, 1, 78, 
	1, 78, 78, 70, 71, 1, 1, 69, 
	79, 1, 1, 1, 78, 1, 78, 78, 
	70, 71, 76, 77, 1, 69, 1, 1, 
	1, 1, 70, 66, 1, 3, 80, 80, 
	80, 80, 80, 80, 80, 80, 80, 1, 
	3, 81, 81, 81, 81, 81, 81, 81, 
	81, 81, 1, 3, 82, 82, 82, 82, 
	82, 82, 82, 82, 82, 1, 3, 83, 
	83, 83, 83, 83, 83, 83, 83, 83, 
	1, 3, 84, 84, 84, 84, 84, 84, 
	84, 84, 84, 1, 3, 85, 85, 85, 
	85, 85, 85, 85, 85, 85, 1, 3, 
	86, 86, 86, 86, 86, 86, 86, 86, 
	86, 1, 3, 87, 87, 87, 87, 87, 
	87, 87, 87, 87, 1, 3, 88, 88, 
	88, 88, 88, 88, 88, 88, 88, 1, 
	3, 89, 89, 89, 89, 89, 89, 89, 
	89, 89, 1, 3, 90, 90, 90, 90, 
	90, 90, 90, 90, 90, 1, 3, 91, 
	91, 91, 91, 91, 91, 91, 91, 91, 
	1, 3, 92, 92, 92, 92, 92, 92, 
	92, 92, 92, 1, 3, 93, 93, 93, 
	93, 93, 93, 93, 93, 93, 1, 3, 
	94, 94, 94, 94, 94, 94, 94, 94, 
	94, 1, 3, 95, 95, 95, 95, 95, 
	95, 95, 95, 95, 1, 3, 96, 96, 
	96, 96, 96, 96, 96, 96, 96, 1, 
	3, 97, 97, 97, 97, 97, 97, 97, 
	97, 97, 1, 3, 1, 3, 4, 98, 
	4, 4, 4, 4, 4, 4, 4, 4, 
	1, 3, 80, 99, 80, 80, 80, 80, 
	80, 80, 80, 80, 1, 100, 81, 81, 
	81, 81, 81, 81, 81, 81, 81, 1, 
	101, 102, 103, 103, 1, 104, 105, 8, 
	106, 1, 108, 109, 42, 1, 110, 1, 
	1, 107, 112, 113, 45, 1, 114, 1, 
	1, 111, 115, 115, 115, 1, 111, 111, 
	111, 1, 117, 118, 49, 119, 120, 121, 
	1, 1, 116, 122, 122, 122, 1, 116, 
	116, 116, 1, 124, 125, 55, 126, 127, 
	1, 1, 123, 129, 130, 59, 131, 132, 
	1, 1, 128, 133, 133, 133, 1, 128, 
	128, 128, 1, 134, 134, 1, 135, 135, 
	1, 136, 136, 1, 137, 138, 138, 1, 
	139, 1, 140, 1, 142, 1, 1, 144, 
	143, 1, 1, 1, 143, 1, 143, 143, 
	141, 142, 1, 1, 140, 1, 1, 1, 
	1, 141, 145, 145, 145, 1, 141, 141, 
	141, 1, 142, 147, 148, 1, 140, 146, 
	1, 1, 1, 146, 1, 146, 146, 141, 
	142, 147, 1, 140, 1, 1, 1, 148, 
	1, 141, 142, 1, 1, 140, 1, 1, 
	1, 149, 1, 149, 149, 141, 142, 1, 
	1, 140, 150, 1, 1, 1, 149, 1, 
	149, 149, 141, 142, 147, 148, 1, 140, 
	1, 1, 1, 1, 141, 137, 1, 151, 
	152, 152, 152, 1, 153, 154, 151, 155, 
	152, 152, 152, 1, 153, 1, 156, 157, 
	158, 152, 152, 152, 1, 159, 160, 161, 
	1, 160, 1, 156, 1, 156, 157, 158, 
	162, 158, 163, 162, 162, 162, 162, 162, 
	162, 162, 162, 1, 156, 157, 162, 158, 
	163, 162, 162, 162, 162, 162, 162, 162, 
	162, 1, 156, 157, 163, 158, 163, 163, 
	163, 163, 163, 163, 163, 163, 1, 153, 
	154, 155, 164, 155, 165, 164, 164, 164, 
	164, 164, 164, 164, 164, 1, 153, 154, 
	164, 155, 165, 164, 164, 164, 164, 164, 
	164, 164, 164, 1, 153, 154, 165, 155, 
	165, 165, 165, 165, 165, 165, 165, 165, 
	1, 166, 167, 168, 166, 169, 169, 169, 
	169, 169, 169, 169, 169, 169, 1, 171, 
	172, 173, 171, 1, 1, 170, 175, 176, 
	1, 1, 1, 174, 177, 1, 167, 1, 
	178, 179, 178, 178, 178, 178, 178, 178, 
	178, 178, 1, 181, 182, 183, 181, 1, 
	1, 180, 185, 186, 1, 1, 1, 184, 
	1, 1, 1, 0
};

static const char _http_parser_trans_targs[] = {
	2, 0, 68, 3, 49, 4, 26, 33, 
	5, 22, 6, 7, 8, 9, 10, 11, 
	12, 13, 14, 17, 15, 122, 18, 19, 
	16, 15, 14, 17, 16, 14, 17, 14, 
	19, 20, 21, 20, 14, 17, 21, 14, 
	17, 23, 5, 24, 23, 5, 24, 25, 
	26, 5, 22, 27, 29, 28, 30, 5, 
	22, 31, 30, 5, 22, 31, 32, 34, 
	35, 36, 37, 48, 38, 39, 40, 41, 
	43, 45, 42, 43, 26, 44, 46, 47, 
	50, 51, 52, 53, 54, 55, 56, 57, 
	58, 59, 60, 61, 62, 63, 64, 65, 
	66, 67, 69, 70, 71, 72, 77, 84, 
	122, 18, 73, 74, 122, 18, 75, 74, 
	122, 18, 75, 76, 77, 122, 18, 73, 
	78, 80, 79, 81, 122, 18, 73, 82, 
	81, 122, 18, 73, 82, 83, 85, 86, 
	87, 88, 99, 89, 90, 91, 92, 94, 
	96, 93, 94, 77, 95, 97, 98, 101, 
	103, 123, 102, 111, 104, 107, 108, 105, 
	100, 106, 109, 110, 112, 113, 115, 124, 
	118, 119, 116, 115, 114, 117, 116, 114, 
	117, 114, 119, 120, 121, 120, 114, 117, 
	121, 114, 117
};

static const char _http_parser_trans_actions[] = {
	1, 0, 1, 15, 0, 1, 1, 39, 
	19, 19, 1, 0, 0, 0, 0, 0, 
	0, 0, 25, 25, 0, 31, 0, 45, 
	9, 9, 51, 51, 0, 13, 13, 0, 
	3, 7, 9, 9, 48, 48, 0, 11, 
	11, 1, 42, 1, 0, 21, 0, 0, 
	0, 66, 66, 0, 27, 0, 23, 73, 
	73, 23, 0, 63, 63, 0, 0, 5, 
	5, 5, 17, 5, 0, 0, 0, 0, 
	1, 1, 0, 0, 54, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 15, 1, 1, 39, 
	57, 19, 19, 1, 69, 42, 1, 0, 
	60, 21, 0, 0, 0, 81, 66, 66, 
	0, 27, 0, 23, 85, 73, 73, 23, 
	0, 77, 63, 63, 0, 0, 5, 5, 
	5, 17, 5, 0, 0, 0, 0, 1, 
	1, 0, 0, 54, 0, 0, 0, 29, 
	29, 35, 0, 0, 0, 0, 0, 37, 
	0, 0, 0, 0, 0, 0, 0, 33, 
	0, 45, 9, 9, 51, 51, 0, 13, 
	13, 0, 3, 7, 9, 9, 48, 48, 
	0, 11, 11
};

static const int http_parser_start = 1;
static const int http_parser_first_final = 122;
static const int http_parser_error = 0;

static const int http_parser_en_ChunkedBody = 100;
static const int http_parser_en_ChunkedBody_chunk_chunk_end = 105;
static const int http_parser_en_Trailers = 114;
static const int http_parser_en_main = 1;


#line 435 "ext/unicorn_http/unicorn_http.rl"

static void http_parser_init(struct http_parser *hp)
{
  int cs = 0;
  hp->flags = 0;
  hp->mark = 0;
  hp->offset = 0;
  hp->start.field = 0;
  hp->s.field_len = 0;
  hp->len.content = 0;
  hp->cont = Qfalse; /* zero on MRI, should be optimized away by above */
  
#line 752 "ext/unicorn_http/unicorn_http.c"
	{
	cs = http_parser_start;
	}

#line 447 "ext/unicorn_http/unicorn_http.rl"
  hp->cs = cs;
}

/** exec **/
static void
http_parser_execute(struct http_parser *hp, char *buffer, size_t len)
{
  const char *p, *pe;
  int cs = hp->cs;
  size_t off = hp->offset;

  if (cs == http_parser_first_final)
    return;

  assert(off <= len && "offset past end of buffer");

  p = buffer+off;
  pe = buffer+len;

  assert((void *)(pe - p) == (void *)(len - off) &&
         "pointers aren't same distance");

  if (HP_FL_TEST(hp, INCHUNK)) {
    HP_FL_UNSET(hp, INCHUNK);
    goto skip_chunk_data_hack;
  }
  
#line 785 "ext/unicorn_http/unicorn_http.c"
	{
	int _klen;
	unsigned int _trans;
	const char *_acts;
	unsigned int _nacts;
	const char *_keys;

	if ( p == pe )
		goto _test_eof;
	if ( cs == 0 )
		goto _out;
_resume:
	_keys = _http_parser_trans_keys + _http_parser_key_offsets[cs];
	_trans = _http_parser_index_offsets[cs];

	_klen = _http_parser_single_lengths[cs];
	if ( _klen > 0 ) {
		const char *_lower = _keys;
		const char *_mid;
		const char *_upper = _keys + _klen - 1;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + ((_upper-_lower) >> 1);
			if ( (*p) < *_mid )
				_upper = _mid - 1;
			else if ( (*p) > *_mid )
				_lower = _mid + 1;
			else {
				_trans += (unsigned int)(_mid - _keys);
				goto _match;
			}
		}
		_keys += _klen;
		_trans += _klen;
	}

	_klen = _http_parser_range_lengths[cs];
	if ( _klen > 0 ) {
		const char *_lower = _keys;
		const char *_mid;
		const char *_upper = _keys + (_klen<<1) - 2;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + (((_upper-_lower) >> 1) & ~1);
			if ( (*p) < _mid[0] )
				_upper = _mid - 2;
			else if ( (*p) > _mid[1] )
				_lower = _mid + 2;
			else {
				_trans += (unsigned int)((_mid - _keys)>>1);
				goto _match;
			}
		}
		_trans += _klen;
	}

_match:
	_trans = _http_parser_indicies[_trans];
	cs = _http_parser_trans_targs[_trans];

	if ( _http_parser_trans_actions[_trans] == 0 )
		goto _again;

	_acts = _http_parser_actions + _http_parser_trans_actions[_trans];
	_nacts = (unsigned int) *_acts++;
	while ( _nacts-- > 0 )
	{
		switch ( *_acts++ )
		{
	case 0:
#line 327 "ext/unicorn_http/unicorn_http.rl"
	{MARK(mark, p); }
	break;
	case 1:
#line 329 "ext/unicorn_http/unicorn_http.rl"
	{ MARK(start.field, p); }
	break;
	case 2:
#line 330 "ext/unicorn_http/unicorn_http.rl"
	{ snake_upcase_char(deconst(p)); }
	break;
	case 3:
#line 331 "ext/unicorn_http/unicorn_http.rl"
	{ downcase_char(deconst(p)); }
	break;
	case 4:
#line 332 "ext/unicorn_http/unicorn_http.rl"
	{ hp->s.field_len = LEN(start.field, p); }
	break;
	case 5:
#line 333 "ext/unicorn_http/unicorn_http.rl"
	{ MARK(mark, p); }
	break;
	case 6:
#line 334 "ext/unicorn_http/unicorn_http.rl"
	{ write_value(hp, buffer, p); }
	break;
	case 7:
#line 335 "ext/unicorn_http/unicorn_http.rl"
	{ write_cont_value(hp, buffer, p); }
	break;
	case 8:
#line 336 "ext/unicorn_http/unicorn_http.rl"
	{ request_method(hp, PTR_TO(mark), LEN(mark, p)); }
	break;
	case 9:
#line 337 "ext/unicorn_http/unicorn_http.rl"
	{
    rb_hash_aset(hp->env, g_rack_url_scheme, STR_NEW(mark, p));
  }
	break;
	case 10:
#line 340 "ext/unicorn_http/unicorn_http.rl"
	{ rb_hash_aset(hp->env, g_http_host, STR_NEW(mark, p)); }
	break;
	case 11:
#line 341 "ext/unicorn_http/unicorn_http.rl"
	{
    VALUE str;

    VALIDATE_MAX_URI_LENGTH(LEN(mark, p), REQUEST_URI);
    str = rb_hash_aset(hp->env, g_request_uri, STR_NEW(mark, p));
    /*
     * "OPTIONS * HTTP/1.1\r\n" is a valid request, but we can't have '*'
     * in REQUEST_PATH or PATH_INFO or else Rack::Lint will complain
     */
    if (STR_CSTR_EQ(str, "*")) {
      str = rb_str_new(NULL, 0);
      rb_hash_aset(hp->env, g_path_info, str);
      rb_hash_aset(hp->env, g_request_path, str);
    }
  }
	break;
	case 12:
#line 356 "ext/unicorn_http/unicorn_http.rl"
	{
    VALIDATE_MAX_URI_LENGTH(LEN(mark, p), FRAGMENT);
    rb_hash_aset(hp->env, g_fragment, STR_NEW(mark, p));
  }
	break;
	case 13:
#line 360 "ext/unicorn_http/unicorn_http.rl"
	{MARK(start.query, p); }
	break;
	case 14:
#line 361 "ext/unicorn_http/unicorn_http.rl"
	{
    VALIDATE_MAX_URI_LENGTH(LEN(start.query, p), QUERY_STRING);
    rb_hash_aset(hp->env, g_query_string, STR_NEW(start.query, p));
  }
	break;
	case 15:
#line 365 "ext/unicorn_http/unicorn_http.rl"
	{ http_version(hp, PTR_TO(mark), LEN(mark, p)); }
	break;
	case 16:
#line 366 "ext/unicorn_http/unicorn_http.rl"
	{
    VALUE val;

    VALIDATE_MAX_URI_LENGTH(LEN(mark, p), REQUEST_PATH);
    val = rb_hash_aset(hp->env, g_request_path, STR_NEW(mark, p));

    /* rack says PATH_INFO must start with "/" or be empty */
    if (!STR_CSTR_EQ(val, "*"))
      rb_hash_aset(hp->env, g_path_info, val);
  }
	break;
	case 17:
#line 376 "ext/unicorn_http/unicorn_http.rl"
	{
    hp->len.chunk = step_incr(hp->len.chunk, (*p), 16);
    if (hp->len.chunk < 0)
      parser_raise(eHttpParserError, "invalid chunk size");
  }
	break;
	case 18:
#line 381 "ext/unicorn_http/unicorn_http.rl"
	{
    finalize_header(hp);

    cs = http_parser_first_final;
    if (HP_FL_TEST(hp, HASBODY)) {
      HP_FL_SET(hp, INBODY);
      if (HP_FL_TEST(hp, CHUNKED))
        cs = http_parser_en_ChunkedBody;
    } else {
      HP_FL_SET(hp, REQEOF);
      assert(!HP_FL_TEST(hp, CHUNKED) && "chunked encoding without body!");
    }
    /*
     * go back to Ruby so we can call the Rack application, we'll reenter
     * the parser iff the body needs to be processed.
     */
    goto post_exec;
  }
	break;
	case 19:
#line 400 "ext/unicorn_http/unicorn_http.rl"
	{
    cs = http_parser_first_final;
    goto post_exec;
  }
	break;
	case 20:
#line 405 "ext/unicorn_http/unicorn_http.rl"
	{
    HP_FL_SET(hp, INTRAILER);
    cs = http_parser_en_Trailers;
    ++p;
    assert(p <= pe && "buffer overflow after chunked body");
    goto post_exec;
  }
	break;
	case 21:
#line 413 "ext/unicorn_http/unicorn_http.rl"
	{
  skip_chunk_data_hack: {
    size_t nr = MIN((size_t)hp->len.chunk, REMAINING);
    memcpy(RSTRING_PTR(hp->cont) + hp->s.dest_offset, p, nr);
    hp->s.dest_offset += nr;
    hp->len.chunk -= nr;
    p += nr;
    assert(hp->len.chunk >= 0 && "negative chunk length");
    if ((size_t)hp->len.chunk > REMAINING) {
      HP_FL_SET(hp, INCHUNK);
      goto post_exec;
    } else {
      p--;
      {cs = 105;goto _again;}
    }
  }}
	break;
#line 1023 "ext/unicorn_http/unicorn_http.c"
		}
	}

_again:
	if ( cs == 0 )
		goto _out;
	if ( ++p != pe )
		goto _resume;
	_test_eof: {}
	_out: {}
	}

#line 474 "ext/unicorn_http/unicorn_http.rl"
post_exec: /* "_out:" also goes here */
  if (hp->cs != http_parser_error)
    hp->cs = cs;
  hp->offset = ulong2uint(p - buffer);

  assert(p <= pe && "buffer overflow after parsing execute");
  assert(hp->offset <= len && "offset longer than length");
}

static void hp_mark(void *ptr)
{
  struct http_parser *hp = ptr;

  rb_gc_mark(hp->buf);
  rb_gc_mark(hp->env);
  rb_gc_mark(hp->cont);
}

static size_t hp_memsize(const void *ptr)
{
  return sizeof(struct http_parser);
}

static const rb_data_type_t hp_type = {
  "unicorn_http",
  { hp_mark, RUBY_TYPED_DEFAULT_FREE, hp_memsize, /* reserved */ },
  /* parent, data, [ flags ] */
};

static struct http_parser *data_get(VALUE self)
{
  struct http_parser *hp;

  TypedData_Get_Struct(self, struct http_parser, &hp_type, hp);
  assert(hp && "failed to extract http_parser struct");
  return hp;
}

/*
 * set rack.url_scheme to "https" or "http", no others are allowed by Rack
 * this resembles the Rack::Request#scheme method as of rack commit
 * 35bb5ba6746b5d346de9202c004cc926039650c7
 */
static void set_url_scheme(VALUE env, VALUE *server_port)
{
  VALUE scheme = rb_hash_aref(env, g_rack_url_scheme);

  if (NIL_P(scheme)) {
    /*
     * would anybody be horribly opposed to removing the X-Forwarded-SSL
     * and X-Forwarded-Proto handling from this parser?  We've had it
     * forever and nobody has said anything against it, either.
     * Anyways, please send comments to our public mailing list:
     * unicorn-public@yhbt.net (no HTML mail, no subscription necessary)
     */
    scheme = rb_hash_aref(env, g_http_x_forwarded_ssl);
    if (!NIL_P(scheme) && STR_CSTR_EQ(scheme, "on")) {
      *server_port = g_port_443;
      scheme = g_https;
    } else {
      scheme = rb_hash_aref(env, g_http_x_forwarded_proto);
      if (NIL_P(scheme)) {
        scheme = g_http;
      } else {
        long len = RSTRING_LEN(scheme);
        if (len >= 5 && !memcmp(RSTRING_PTR(scheme), "https", 5)) {
          if (len != 5)
            scheme = g_https;
          *server_port = g_port_443;
        } else {
          scheme = g_http;
        }
      }
    }
    rb_hash_aset(env, g_rack_url_scheme, scheme);
  } else if (STR_CSTR_EQ(scheme, "https")) {
    *server_port = g_port_443;
  } else {
    assert(*server_port == g_port_80 && "server_port not set");
  }
}

/*
 * Parse and set the SERVER_NAME and SERVER_PORT variables
 * Not supporting X-Forwarded-Host/X-Forwarded-Port in here since
 * anybody who needs them is using an unsupported configuration and/or
 * incompetent.  Rack::Request will handle X-Forwarded-{Port,Host} just
 * fine.
 */
static void set_server_vars(VALUE env, VALUE *server_port)
{
  VALUE server_name = g_localhost;
  VALUE host = rb_hash_aref(env, g_http_host);

  if (!NIL_P(host)) {
    char *host_ptr = RSTRING_PTR(host);
    long host_len = RSTRING_LEN(host);
    char *colon;

    if (*host_ptr == '[') { /* ipv6 address format */
      char *rbracket = memchr(host_ptr + 1, ']', host_len - 1);

      if (rbracket)
        colon = (rbracket[1] == ':') ? rbracket + 1 : NULL;
      else
        colon = memchr(host_ptr + 1, ':', host_len - 1);
    } else {
      colon = memchr(host_ptr, ':', host_len);
    }

    if (colon) {
      long port_start = colon - host_ptr + 1;

      server_name = rb_str_substr(host, 0, colon - host_ptr);
      if ((host_len - port_start) > 0)
        *server_port = rb_str_substr(host, port_start, host_len);
    } else {
      server_name = host;
    }
  }
  rb_hash_aset(env, g_server_name, server_name);
  rb_hash_aset(env, g_server_port, *server_port);
}

static void finalize_header(struct http_parser *hp)
{
  VALUE server_port = g_port_80;

  set_url_scheme(hp->env, &server_port);
  set_server_vars(hp->env, &server_port);

  if (!HP_FL_TEST(hp, HASHEADER))
    rb_hash_aset(hp->env, g_server_protocol, g_http_09);

  /* rack requires QUERY_STRING */
  if (NIL_P(rb_hash_aref(hp->env, g_query_string)))
    rb_hash_aset(hp->env, g_query_string, rb_str_new(NULL, 0));
}

static VALUE HttpParser_alloc(VALUE klass)
{
  struct http_parser *hp;

  return TypedData_Make_Struct(klass, struct http_parser, &hp_type, hp);
}

/**
 * call-seq:
 *    parser.new => parser
 *
 * Creates a new parser.
 */
static VALUE HttpParser_init(VALUE self)
{
  struct http_parser *hp = data_get(self);

  http_parser_init(hp);
  hp->buf = rb_str_new(NULL, 0);
  hp->env = rb_hash_new();

  return self;
}

/**
 * call-seq:
 *    parser.clear => parser
 *
 * Resets the parser to it's initial state so that you can reuse it
 * rather than making new ones.
 */
static VALUE HttpParser_clear(VALUE self)
{
  struct http_parser *hp = data_get(self);

  /* we can't safely reuse .buf and .env if hijacked */
  if (HP_FL_TEST(hp, HIJACK))
    return HttpParser_init(self);

  http_parser_init(hp);
  my_hash_clear(hp->env);

  return self;
}

static void advance_str(VALUE str, off_t nr)
{
  long len = RSTRING_LEN(str);

  if (len == 0)
    return;

  rb_str_modify(str);

  assert(nr <= len && "trying to advance past end of buffer");
  len -= nr;
  if (len > 0) /* unlikely, len is usually 0 */
    memmove(RSTRING_PTR(str), RSTRING_PTR(str) + nr, len);
  rb_str_set_len(str, len);
}

/**
 * call-seq:
 *   parser.content_length => nil or Integer
 *
 * Returns the number of bytes left to run through HttpParser#filter_body.
 * This will initially be the value of the "Content-Length" HTTP header
 * after header parsing is complete and will decrease in value as
 * HttpParser#filter_body is called for each chunk.  This should return
 * zero for requests with no body.
 *
 * This will return nil on "Transfer-Encoding: chunked" requests.
 */
static VALUE HttpParser_content_length(VALUE self)
{
  struct http_parser *hp = data_get(self);

  return HP_FL_TEST(hp, CHUNKED) ? Qnil : OFFT2NUM(hp->len.content);
}

/**
 * Document-method: parse
 * call-seq:
 *    parser.parse => env or nil
 *
 * Takes a Hash and a String of data, parses the String of data filling
 * in the Hash returning the Hash if parsing is finished, nil otherwise
 * When returning the env Hash, it may modify data to point to where
 * body processing should begin.
 *
 * Raises HttpParserError if there are parsing errors.
 */
static VALUE HttpParser_parse(VALUE self)
{
  struct http_parser *hp = data_get(self);
  VALUE data = hp->buf;

  if (HP_FL_TEST(hp, TO_CLEAR))
    HttpParser_clear(self);

  http_parser_execute(hp, RSTRING_PTR(data), RSTRING_LEN(data));
  if (hp->offset > MAX_HEADER_LEN)
    parser_raise(e413, "HTTP header is too large");

  if (hp->cs == http_parser_first_final ||
      hp->cs == http_parser_en_ChunkedBody) {
    advance_str(data, hp->offset + 1);
    hp->offset = 0;
    if (HP_FL_TEST(hp, INTRAILER))
      HP_FL_SET(hp, REQEOF);

    return hp->env;
  }

  if (hp->cs == http_parser_error)
    parser_raise(eHttpParserError, "Invalid HTTP format, parsing fails.");

  return Qnil;
}

/**
 * Document-method: parse
 * call-seq:
 *    parser.add_parse(buffer) => env or nil
 *
 * adds the contents of +buffer+ to the internal buffer and attempts to
 * continue parsing.  Returns the +env+ Hash on success or nil if more
 * data is needed.
 *
 * Raises HttpParserError if there are parsing errors.
 */
static VALUE HttpParser_add_parse(VALUE self, VALUE buffer)
{
  struct http_parser *hp = data_get(self);

  Check_Type(buffer, T_STRING);
  rb_str_buf_append(hp->buf, buffer);

  return HttpParser_parse(self);
}

/**
 * Document-method: trailers
 * call-seq:
 *    parser.trailers(req, data) => req or nil
 *
 * This is an alias for HttpParser#headers
 */

/**
 * Document-method: headers
 */
static VALUE HttpParser_headers(VALUE self, VALUE env, VALUE buf)
{
  struct http_parser *hp = data_get(self);

  hp->env = env;
  hp->buf = buf;

  return HttpParser_parse(self);
}

static int chunked_eof(struct http_parser *hp)
{
  return ((hp->cs == http_parser_first_final) || HP_FL_TEST(hp, INTRAILER));
}

/**
 * call-seq:
 *    parser.body_eof? => true or false
 *
 * Detects if we're done filtering the body or not.  This can be used
 * to detect when to stop calling HttpParser#filter_body.
 */
static VALUE HttpParser_body_eof(VALUE self)
{
  struct http_parser *hp = data_get(self);

  if (HP_FL_TEST(hp, CHUNKED))
    return chunked_eof(hp) ? Qtrue : Qfalse;

  return hp->len.content == 0 ? Qtrue : Qfalse;
}

/**
 * call-seq:
 *    parser.keepalive? => true or false
 *
 * This should be used to detect if a request can really handle
 * keepalives and pipelining.  Currently, the rules are:
 *
 * 1. MUST be a GET or HEAD request
 * 2. MUST be HTTP/1.1 +or+ HTTP/1.0 with "Connection: keep-alive"
 * 3. MUST NOT have "Connection: close" set
 */
static VALUE HttpParser_keepalive(VALUE self)
{
  struct http_parser *hp = data_get(self);

  return HP_FL_ALL(hp, KEEPALIVE) ? Qtrue : Qfalse;
}

/**
 * call-seq:
 *    parser.next? => true or false
 *
 * Exactly like HttpParser#keepalive?, except it will reset the internal
 * parser state on next parse if it returns true.
 */
static VALUE HttpParser_next(VALUE self)
{
  struct http_parser *hp = data_get(self);

  if (HP_FL_ALL(hp, KEEPALIVE)) {
    HP_FL_SET(hp, TO_CLEAR);
    return Qtrue;
  }
  return Qfalse;
}

/**
 * call-seq:
 *    parser.headers? => true or false
 *
 * This should be used to detect if a request has headers (and if
 * the response will have headers as well).  HTTP/0.9 requests
 * should return false, all subsequent HTTP versions will return true
 */
static VALUE HttpParser_has_headers(VALUE self)
{
  struct http_parser *hp = data_get(self);

  return HP_FL_TEST(hp, HASHEADER) ? Qtrue : Qfalse;
}

static VALUE HttpParser_buf(VALUE self)
{
  return data_get(self)->buf;
}

static VALUE HttpParser_env(VALUE self)
{
  return data_get(self)->env;
}

static VALUE HttpParser_hijacked_bang(VALUE self)
{
  struct http_parser *hp = data_get(self);

  HP_FL_SET(hp, HIJACK);

  return self;
}

/**
 * call-seq:
 *    parser.filter_body(dst, src) => nil/src
 *
 * Takes a String of +src+, will modify data if dechunking is done.
 * Returns +nil+ if there is more data left to process.  Returns
 * +src+ if body processing is complete. When returning +src+,
 * it may modify +src+ so the start of the string points to where
 * the body ended so that trailer processing can begin.
 *
 * Raises HttpParserError if there are dechunking errors.
 * Basically this is a glorified memcpy(3) that copies +src+
 * into +buf+ while filtering it through the dechunker.
 */
static VALUE HttpParser_filter_body(VALUE self, VALUE dst, VALUE src)
{
  struct http_parser *hp = data_get(self);
  char *srcptr;
  long srclen;

  srcptr = RSTRING_PTR(src);
  srclen = RSTRING_LEN(src);

  StringValue(dst);

  if (HP_FL_TEST(hp, CHUNKED)) {
    if (!chunked_eof(hp)) {
      rb_str_modify(dst);
      rb_str_resize(dst, srclen); /* we can never copy more than srclen bytes */

      hp->s.dest_offset = 0;
      hp->cont = dst;
      hp->buf = src;
      http_parser_execute(hp, srcptr, srclen);
      if (hp->cs == http_parser_error)
        parser_raise(eHttpParserError, "Invalid HTTP format, parsing fails.");

      assert(hp->s.dest_offset <= hp->offset &&
             "destination buffer overflow");
      advance_str(src, hp->offset);
      rb_str_set_len(dst, hp->s.dest_offset);

      if (RSTRING_LEN(dst) == 0 && chunked_eof(hp)) {
        assert(hp->len.chunk == 0 && "chunk at EOF but more to parse");
      } else {
        src = Qnil;
      }
    }
  } else {
    /* no need to enter the Ragel machine for unchunked transfers */
    assert(hp->len.content >= 0 && "negative Content-Length");
    if (hp->len.content > 0) {
      long nr = MIN(srclen, hp->len.content);

      rb_str_modify(dst);
      rb_str_resize(dst, nr);
      /*
       * using rb_str_replace() to avoid memcpy() doesn't help in
       * most cases because a GC-aware programmer will pass an explicit
       * buffer to env["rack.input"].read and reuse the buffer in a loop.
       * This causes copy-on-write behavior to be triggered anyways
       * when the +src+ buffer is modified (when reading off the socket).
       */
      hp->buf = src;
      memcpy(RSTRING_PTR(dst), srcptr, nr);
      hp->len.content -= nr;
      if (hp->len.content == 0) {
        HP_FL_SET(hp, REQEOF);
        hp->cs = http_parser_first_final;
      }
      advance_str(src, nr);
      src = Qnil;
    }
  }
  hp->offset = 0; /* for trailer parsing */
  return src;
}

static VALUE HttpParser_rssset(VALUE self, VALUE boolean)
{
  struct http_parser *hp = data_get(self);

  if (RTEST(boolean))
    HP_FL_SET(hp, RESSTART);
  else
    HP_FL_UNSET(hp, RESSTART);

  return boolean; /* ignored by Ruby anyways */
}

static VALUE HttpParser_rssget(VALUE self)
{
  struct http_parser *hp = data_get(self);

  return HP_FL_TEST(hp, RESSTART) ? Qtrue : Qfalse;
}

#define SET_GLOBAL(var,str) do { \
  var = find_common_field(str, sizeof(str) - 1); \
  assert(!NIL_P(var) && "missed global field"); \
} while (0)

void Init_unicorn_http(void)
{
  VALUE mUnicorn;

  mUnicorn = rb_define_module("Unicorn");
  cHttpParser = rb_define_class_under(mUnicorn, "HttpParser", rb_cObject);
  eHttpParserError =
         rb_define_class_under(mUnicorn, "HttpParserError", rb_eIOError);
  e413 = rb_define_class_under(mUnicorn, "RequestEntityTooLargeError",
                               eHttpParserError);
  e414 = rb_define_class_under(mUnicorn, "RequestURITooLongError",
                               eHttpParserError);

  init_globals();
  rb_define_alloc_func(cHttpParser, HttpParser_alloc);
  rb_define_method(cHttpParser, "initialize", HttpParser_init, 0);
  rb_define_method(cHttpParser, "clear", HttpParser_clear, 0);
  rb_define_method(cHttpParser, "parse", HttpParser_parse, 0);
  rb_define_method(cHttpParser, "add_parse", HttpParser_add_parse, 1);
  rb_define_method(cHttpParser, "headers", HttpParser_headers, 2);
  rb_define_method(cHttpParser, "trailers", HttpParser_headers, 2);
  rb_define_method(cHttpParser, "filter_body", HttpParser_filter_body, 2);
  rb_define_method(cHttpParser, "content_length", HttpParser_content_length, 0);
  rb_define_method(cHttpParser, "body_eof?", HttpParser_body_eof, 0);
  rb_define_method(cHttpParser, "keepalive?", HttpParser_keepalive, 0);
  rb_define_method(cHttpParser, "headers?", HttpParser_has_headers, 0);
  rb_define_method(cHttpParser, "next?", HttpParser_next, 0);
  rb_define_method(cHttpParser, "buf", HttpParser_buf, 0);
  rb_define_method(cHttpParser, "env", HttpParser_env, 0);
  rb_define_method(cHttpParser, "hijacked!", HttpParser_hijacked_bang, 0);
  rb_define_method(cHttpParser, "response_start_sent=", HttpParser_rssset, 1);
  rb_define_method(cHttpParser, "response_start_sent", HttpParser_rssget, 0);

  /*
   * The maximum size a single chunk when using chunked transfer encoding.
   * This is only a theoretical maximum used to detect errors in clients,
   * it is highly unlikely to encounter clients that send more than
   * several kilobytes at once.
   */
  rb_define_const(cHttpParser, "CHUNK_MAX", OFFT2NUM(UH_OFF_T_MAX));

  /*
   * The maximum size of the body as specified by Content-Length.
   * This is only a theoretical maximum, the actual limit is subject
   * to the limits of the file system used for +Dir.tmpdir+.
   */
  rb_define_const(cHttpParser, "LENGTH_MAX", OFFT2NUM(UH_OFF_T_MAX));

  rb_define_singleton_method(cHttpParser, "max_header_len=", set_maxhdrlen, 1);

  init_common_fields();
  SET_GLOBAL(g_http_host, "HOST");
  SET_GLOBAL(g_http_trailer, "TRAILER");
  SET_GLOBAL(g_http_transfer_encoding, "TRANSFER_ENCODING");
  SET_GLOBAL(g_content_length, "CONTENT_LENGTH");
  SET_GLOBAL(g_http_connection, "CONNECTION");
  id_set_backtrace = rb_intern("set_backtrace");
  init_unicorn_httpdate();

#ifndef HAVE_RB_HASH_CLEAR
  id_clear = rb_intern("clear");
#endif
  id_is_chunked_p = rb_intern("is_chunked?");
}
#undef SET_GLOBAL
