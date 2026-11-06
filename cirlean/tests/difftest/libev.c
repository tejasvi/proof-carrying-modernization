// libevent 2.1 library models: evbuffer_new/add/get_length/free, evhttp_add_header,
// evhttp_send_reply on a request without a connection, event_base_loopbreak.
// Built with libevent 2.1's headers and static library (run.sh: DT_CFLAGS, DT_LIBS).
#include <stdlib.h>
#include <string.h>
#include <event2/buffer.h>
#include <event2/event.h>
#include <event2/http.h>
#include <event2/http_struct.h>
#include <event2/keyvalq_struct.h>

static struct evkeyvalq *new_list(void) {
  struct evkeyvalq *h = malloc(sizeof *h);
  h->tqh_first = NULL;
  h->tqh_last = &h->tqh_first;
  return h;
}

static int count(struct evkeyvalq *h) {
  int n = 0;
  for (struct evkeyval *e = h->tqh_first; e != NULL; e = e->next.tqe_next) n++;
  return n;
}

// frees what evhttp_add_header allocated (libevent allocates with calloc and strdup)
static void free_list(struct evkeyvalq *h) {
  struct evkeyval *e = h->tqh_first;
  while (e != NULL) {
    struct evkeyval *nx = e->next.tqe_next;
    free(e->key);
    free(e->value);
    free(e);
    e = nx;
  }
  free(h);
}

// a request as evhttp_request_new leaves it, without buffers and without a connection
static struct evhttp_request *new_req(void) {
  struct evhttp_request *req = calloc(1, sizeof *req);
  req->input_headers = new_list();
  req->output_headers = new_list();
  return req;
}

int t_buf_new(int x) {
  struct evbuffer *b = evbuffer_new();
  int r = b != NULL;
  evbuffer_free(b);
  return r + x;
}

int t_buf_add(int x) {
  struct evbuffer *b = evbuffer_new();
  char s[] = "hello";
  int r = evbuffer_add(b, s, 5);
  int r2 = evbuffer_add(b, s, (size_t)x);
  int n = (int)evbuffer_get_length(b);
  evbuffer_free(b);
  return r * 1000 + r2 * 100 + n;
}

int t_buf_add_zero(int x) {
  struct evbuffer *b = evbuffer_new();
  char c = 'a';
  int r = evbuffer_add(b, &c, 0);
  int n = (int)evbuffer_get_length(b);
  evbuffer_free(b);
  return r * 10 + n + x;
}

// libevent copies with memcpy(dst, NULL, 0): undefined (C11 7.1.4p1)
int ub_buf_add_null0(int x) {
  struct evbuffer *b = evbuffer_new();
  int r = evbuffer_add(b, NULL, 0);
  evbuffer_free(b);
  return r + x;
}

int ub_buf_double_free(int x) {
  struct evbuffer *b = evbuffer_new();
  evbuffer_free(b);
  evbuffer_free(b);
  return x;
}

int t_hdr_add(int x) {
  struct evkeyvalq *h = new_list();
  int r1 = evhttp_add_header(h, "Content-Type", "application/x-thrift");
  int r2 = evhttp_add_header(h, "X-A", "1");
  if (r1 != 0 || r2 != 0) return -1;
  struct evkeyval *a = h->tqh_first, *b = a->next.tqe_next;
  int ok = strcmp(a->key, "Content-Type") == 0 && strcmp(a->value, "application/x-thrift") == 0 &&
           strcmp(b->key, "X-A") == 0 && strcmp(b->value, "1") == 0 && b->next.tqe_next == NULL &&
           b->next.tqe_prev == &a->next.tqe_next && a->next.tqe_prev == &h->tqh_first &&
           h->tqh_last == &b->next.tqe_next;
  int n = count(h);
  free_list(h);
  return ok * 100 + n * 10 + x;
}

int t_hdr_cr_key(int x) {
  struct evkeyvalq *h = new_list();
  int r = evhttp_add_header(h, "Bad\rKey", "v");
  int n = count(h);
  free_list(h);
  return r * 10 + n + x;
}

int t_hdr_lf_value(int x) {
  struct evkeyvalq *h = new_list();
  int r = evhttp_add_header(h, "K", "a\nb");
  int n = count(h);
  free_list(h);
  return r * 10 + n + x;
}

// folded values (a line break followed by a space or a tab): libevent 2.1.12 refuses them too
int t_hdr_fold(int x) {
  struct evkeyvalq *h = new_list();
  int r1 = evhttp_add_header(h, "K", "a\r\n b");
  int r2 = evhttp_add_header(h, "L", "c\n\td");
  int n = count(h);
  free_list(h);
  return r1 * 100 + r2 * 10 + n + x;
}

// which values evhttp_add_header accepts: bit i for value i
int t_hdr_values(int x) {
  static const char *vs[] = {"a b", "a\tb", "a\rb", "a\nb", "a\r\n b", "a\n\tb", "\r\n b", "a\r\n", "ab\x01", "a\x7f"};
  struct evkeyvalq *h = new_list();
  int mask = 0;
  for (int i = 0; i < 10; i++)
    if (evhttp_add_header(h, "K", vs[i]) == 0) mask |= 1 << i;
  int n = count(h);
  free_list(h);
  return mask * 100 + n + x;
}

// which keys evhttp_add_header accepts: bit i for key i
int t_hdr_keys(int x) {
  static const char *ks[] = {"K", "Bad Key", "Bad:Key", "", "Bad\tKey", "Bad\x01Key", "Bad\nKey"};
  struct evkeyvalq *h = new_list();
  int mask = 0;
  for (int i = 0; i < 7; i++)
    if (evhttp_add_header(h, ks[i], "v") == 0) mask |= 1 << i;
  free_list(h);
  return mask + x;
}

int t_hdr_trailing_nl(int x) {
  struct evkeyvalq *h = new_list();
  int r = evhttp_add_header(h, "K", "abc\r\n");
  int n = count(h);
  free_list(h);
  return r * 10 + n + x;
}

// no connection: libevent frees the request at once; what happens to databuf?
int t_reply_nocon(int x) {
  struct evhttp_request *req = new_req();
  evhttp_add_header(req->output_headers, "Content-Type", "text/plain");
  struct evbuffer *b = evbuffer_new();
  evbuffer_add(b, "abc", 3);
  evhttp_send_reply(req, 200, "OK", b);
  int n = (int)evbuffer_get_length(b);
  evbuffer_free(b);
  return n + x;
}

int t_reply_nocon_nullbuf(int x) {
  struct evhttp_request *req = new_req();
  evhttp_add_header(req->input_headers, "Host", "example.org");
  evhttp_send_reply(req, 404, NULL, NULL);
  return x;
}

// the request was freed by evhttp_send_reply
int ub_reply_use_after(int x) {
  struct evhttp_request *req = new_req();
  evhttp_send_reply(req, 200, "OK", NULL);
  return req->response_code + x;
}

// libevent empties a null header list: undefined
int ub_reply_null_headers(int x) {
  struct evhttp_request *req = calloc(1, sizeof *req);
  evhttp_send_reply(req, 200, "OK", NULL);
  return x;
}

int t_loopbreak_null(int x) {
  return event_base_loopbreak(NULL) * 10 + x;
}
