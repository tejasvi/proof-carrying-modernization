/* The cheap census batch (C sources), run with MODE=status CASES=cheap1_cases.txt: signbit and
   the fcNegative / fcPositive classes, rint / nearbyint / lrint in the default rounding mode
   (to nearest, half to even), perror, signal (registering only: no signal is delivered), memchr
   and posix_memalign. Expected result, labelled per case in the cases file: MATCH, or UB from
   cirrun. */
#include <math.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* signbit: zeros and infinities included, float, double and long double */
int t_signbit(int k) {
  double nz = -0.0, pz = 0.0, m = -1.5, p = 2.0;
  float fz = -0.0f;
  long double lm = -3.0L;
  return (signbit(nz) != 0) + 2 * (signbit(pz) != 0) + 4 * (signbit(m) != 0) + 8 * (signbit(p) != 0) +
         16 * (signbit(-INFINITY) != 0) + 32 * (signbit(fz) != 0) + 64 * (signbit(lm) != 0) + k;
}
/* clang's __builtin_isfpclass with LLVM's fcNegative (0x3c) and fcPositive (0x3c0), which have no
   NaN; gcc, which builds the native side, has no such builtin: the same classes in standard C */
#ifdef __clang__
#define IS_NEG(x) __builtin_isfpclass(x, 0x3c)
#define IS_POS(x) __builtin_isfpclass(x, 0x3c0)
#else
#define IS_NEG(x) (!isnan(x) && signbit(x) != 0)
#define IS_POS(x) (!isnan(x) && signbit(x) == 0)
#endif
int t_fpclass_sign(int k) {
  double v[6] = {-2.0, -0.0, 0.0, 1e-310, -INFINITY, NAN};
  int r = 0;
  for (int i = 0; i < 6; i++)
    r = r * 4 + IS_NEG(v[i]) + 2 * IS_POS(v[i]);
  return r % 251 + k;
}
/* rint and nearbyint: half to even, the sign of a zero result kept */
int t_rint(int k) {
  return (int)rint(2.5) + 10 * (int)rint(3.5) + 100 * (rint(-2.5) == -2.0) +
         (int)nearbyint(1.5) * 3 + (signbit(rint(-0.4)) != 0) * 7 + (int)rintf(0.5f) + k;
}
int t_lrint(int k) {
  long a = lrint(2.5), b = lrint(-3.5);
  long long c = llrint(10000000000.5);
  long d = lrintf(-0.5f);
  return (int)(a + 10 * (b + 4) + (c == 10000000000LL) * 20 + d * 5) + 50 + k;
}
/* lrint of a value out of the range of long: unspecified (C11 7.12.9.5) */
int t_lrint_range(int k) { return lrint(1e30) == 0 ? 1 + k : 2 + k; }

int t_perror(int k) {
  perror("cheap1");
  return 3 + k;
}
int t_perror_null(int k) {
  perror(NULL);
  return 4 + k;
}

static void h1(int s) { (void)s; }
static void h2(int s) { (void)s; }
int t_signal_prev(int k) {
  void (*o1)(int) = signal(SIGINT, h1);
  void (*o2)(int) = signal(SIGINT, h2);
  void (*o3)(int) = signal(SIGTERM, SIG_IGN);
  void (*o4)(int) = signal(SIGTERM, SIG_DFL);
  return (o1 == SIG_DFL) + 2 * (o2 == h1) + 4 * (o3 == SIG_DFL) + 8 * (o4 == SIG_IGN) + k;
}
int t_signal_err(int k) {
  return (signal(SIGKILL, h1) == SIG_ERR) + 2 * (signal(SIGSTOP, h1) == SIG_ERR) + 4 * (signal(0, h1) == SIG_ERR) +
         8 * (signal(65, h1) == SIG_ERR) + k;
}

int t_memchr(int k) {
  char s[] = "abcdef";
  char *p = memchr(s, 'd', 6);
  char *q = memchr(s, 'z', 6);
  char *r = memchr(s, 'a', 0);
  char *u = memchr(s, 0x100 + 'c', 6);
  return (int)(p - s) + 10 * (q == NULL) + 20 * (r == NULL) + 40 * (int)(u - s) + k;
}
/* the characters are read one by one up to the first match: n may exceed the array */
int t_memchr_stop(int k) {
  char s[4] = {'x', 'y', 'z', 'w'};
  char *p = memchr(s, 'y', 100);
  return (int)(p - s) + 5 + k;
}
/* no match within the array, and n exceeds it */
int t_memchr_past(int k) {
  char s[4] = {'x', 'y', 'z', 'w'};
  return memchr(s, 'q', 100) == NULL ? 6 + k : 7 + k;
}
/* a null pointer, even with n = 0 (C11 7.24.1p2) */
int t_memchr_null(int k) {
  char *volatile n = NULL;
  return memchr(n, 'a', 0) == NULL ? 8 + k : 9 + k;
}

int t_pma(int k) {
  void *p = NULL;
  int r = posix_memalign(&p, 16, 32);
  int *q = p;
  q[0] = 5;
  q[7] = 6;
  int v = q[0] + q[7];
  free(p);
  return (r == 0) * 100 + v + k;
}
int t_pma_einval(int k) {
  void *p = NULL;
  int r1 = posix_memalign(&p, 12, 32);
  int r2 = posix_memalign(&p, 4, 32);
  return r1 + r2 + (p == NULL) + k;
}
