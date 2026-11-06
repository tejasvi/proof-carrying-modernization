/* A program's own functions named like those of libevent and POSIX (threads, scheduling,
   strerror_r), whose names C does not reserve (C11 7.1.3), and glibc's __errno_location: their
   bodies run; the library models attach only to declarations without a body. Built without
   libevent and without <pthread.h>. */
struct evbuffer { int n; };
static struct evbuffer pool;

struct evbuffer *evbuffer_new(void) {
  pool.n = 77;
  return &pool;
}

int x_own_evbuffer_new(int k) {
  struct evbuffer *b = evbuffer_new();
  return b->n + k;
}

/* pthread_t is unsigned long in glibc */
unsigned long pthread_self(void) { return 42; }
int pthread_equal(unsigned long a, unsigned long b) { return a + b == 5; }

int x_own_pthread_self(int k) { return (int)pthread_self() + k; }
int x_own_pthread_equal(int k) { return pthread_equal(2, 3) * 10 + pthread_equal(1, 1) + k; }

/* POSIX scheduling and strerror_r (built without <sched.h> and <string.h>); and glibc's
   __errno_location, a name C reserves (C11 7.1.3: defining it is undefined, so its body running is
   one of the outcomes allowed), whose model attaches only to a declaration too */
struct sched_param { int sched_priority; };
int sched_get_priority_max(int p) { return p + 100; }
int sched_get_priority_min(int p) { return p + 200; }
int pthread_setschedparam(unsigned long t, int p, const struct sched_param *sp) {
  return (int)t * 100 + p * 10 + sp->sched_priority;
}
char *strerror_r(int e, char *buf, unsigned long n) {
  buf[0] = (char)('a' + e);
  buf[1] = 0;
  return n > 1 ? buf : 0;
}
static int own_errno = 9;
int *__errno_location(void) { return &own_errno; }

int x_own_sched_prio(int k) { return sched_get_priority_max(k) * 1000 + sched_get_priority_min(k); }
int x_own_setschedparam(int k) {
  struct sched_param sp = {3};
  return pthread_setschedparam(5, k, &sp);
}
int x_own_strerror_r(int k) {
  char b[4];
  return strerror_r(k, b, sizeof b)[0];
}
int x_own_errno_location(int k) {
  *__errno_location() += k;
  return *__errno_location();
}

/* control: a static function named like a C library function (internal linkage) */
static double sqrt(double x) { return 7.0 + x * 0; }
int x_own_static_sqrt(int k) { return (int)sqrt(4.0 + k); }
