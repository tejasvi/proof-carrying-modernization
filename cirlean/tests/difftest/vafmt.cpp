// The life of a va_list (C11 7.16), the argument types of printf-family conversions (7.21.6.1p9)
// and a negative VLA size (6.7.6.2p5) (CASES=vafmt_cases.txt). The cases labelled UB break those
// rules (natively they do something); the controls keep them.
#include <cstdarg>
#include <cstdio>

// --- va_list: initialized by va_start / va_copy, ended by va_end before the return; va_arg only
// on an initialized one; after a callee's va_arg on it, the caller may only end it (7.16p3)
static int sum(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int s = 0;
  for (int i = 0; i < n; ++i) s += va_arg(ap, int);
  va_end(ap);
  return s;
}
int t_va_ok(int k) { return sum(3, k, 2, 3); }

// va_start again after va_end
static int twice(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = va_arg(ap, int);
  va_end(ap);
  va_start(ap, n);
  int b = va_arg(ap, int);
  va_end(ap);
  return a * 10 + b;
}
int t_va_restart(int k) { return twice(1, k); }

// va_copy into a fresh va_list, both ended
static int copied(int n, ...) {
  va_list ap, cp;
  va_start(ap, n);
  va_copy(cp, ap);
  int a = va_arg(ap, int);
  int b = va_arg(cp, int);
  va_end(cp);
  va_end(ap);
  return a * 10 + b;
}
int t_va_copy_ok(int k) { return copied(1, k); }

// a callee's va_arg on the caller's va_list; the caller then only ends it
static int first(va_list ap) { return va_arg(ap, int); }
static int callee_reads(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = first(ap);
  va_end(ap);
  return a;
}
int t_va_callee_ok(int k) { return callee_reads(1, k); }

// UB: va_arg after va_end (7.16.1.1p2)
static int after_end(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = va_arg(ap, int);
  va_end(ap);
  int b = va_arg(ap, int);
  return a * 10 + b;
}
int t_ub_va_after_end(int k) { return after_end(2, k, 2); }

// UB: va_start again without va_end (7.16.1.4p3)
static int start_twice(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = va_arg(ap, int);
  va_start(ap, n);
  int b = va_arg(ap, int);
  va_end(ap);
  return a * 10 + b;
}
int t_ub_va_start_twice(int k) { return start_twice(2, k, 2); }

// UB: a return without va_end (7.16.1.3p2)
static int no_end(int n, ...) {
  va_list ap;
  va_start(ap, n);
  return va_arg(ap, int);
}
int t_ub_va_no_end(int k) { return no_end(1, k); }

// UB: va_copy into an initialized va_list without va_end (7.16.1.2p2)
static int copy_twice(int n, ...) {
  va_list ap, cp;
  va_start(ap, n);
  va_copy(cp, ap);
  va_copy(cp, ap);
  int a = va_arg(cp, int);
  va_end(cp);
  va_end(ap);
  return a;
}
int t_ub_va_copy_twice(int k) { return copy_twice(1, k); }

// UB: the caller's va_arg after a callee's va_arg on its va_list (7.16p3)
static int callee_then_caller(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = first(ap);
  int b = va_arg(ap, int);
  va_end(ap);
  return a * 10 + b;
}
int t_ub_va_callee_consumes(int k) { return callee_then_caller(2, k, 2); }

// UB: va_end without va_start (7.16.1.3p2)
static int end_twice(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = va_arg(ap, int);
  va_end(ap);
  va_end(ap);
  return a;
}
int t_ub_va_end_twice(int k) { return end_twice(1, k); }

// gap: through a function pointer the arguments keep their values only, so an int read as long
// is not caught (UB in C11 7.16.1.1p2)
static long as_long(int n, ...) {
  va_list ap;
  va_start(ap, n);
  long x = va_arg(ap, long);
  va_end(ap);
  return x;
}
static long (*as_long_ptr)(int, ...) = as_long;
int t_gap_va_fnptr(int k) { return (int)as_long_ptr(1, k); }

// --- printf-family argument types: each argument has the type its conversion needs, after the
// default argument promotions; an argument of the other signedness only when its value fits both
int t_fmt_ok(int k) {
  char b[96];
  signed char sc = (signed char)k;
  unsigned long ul = 7;
  int n = snprintf(b, sizeof b, "%d %ld %u %c %s %f %*d %lu %hhd %x", k, 10L * k, 3u, 65 + k, "s", 0.5, 4, k, ul,
                   sc, 255u);
  return n * 100 + b[0];
}
int t_fmt_u_pos(int k) {
  char b[16];
  return sprintf(b, "%u", k) * 100 + b[0];
}
int t_ub_fmt_d_long(int k) {
  char b[32];
  sprintf(b, "%d", 5L + k);
  return b[0];
}
int t_ub_fmt_ld_int(int k) {
  char b[32];
  sprintf(b, "%ld", 5 + k);
  return b[0];
}
int t_ub_printf_d_long(int k) { return printf("%d\n", 5L + k); }
int t_ub_fmt_star_long(int k) {
  char b[32];
  return sprintf(b, "%*d", 3L, 7 + k);
}
int t_ub_fmt_lld_int(int k) {
  char b[32];
  sprintf(b, "%lld", -5 - k);
  return b[1];
}
int t_ub_fmt_c_long(int k) {
  char b[8];
  sprintf(b, "%c", 65L + k);
  return b[0];
}
int t_ub_fmt_ls_char(int k) {
  char b[16] = "zz";
  int r = sprintf(b, "%ls", "ab");
  return r * 1000 + b[0] + k;
}
int t_ub_fmt_u_neg(int k) {
  char b[16];
  return sprintf(b, "%u", -k);
}
int t_ub_snprintf_d_double(int k) {
  char b[16];
  return snprintf(b, sizeof b, "%d", 1.5 * k);
}

// --- a VLA's size must be positive
int t_vla_pos(int k) {
  volatile int n = k;
  int a[n];
  return (int)sizeof a;
}
int t_ub_vla_neg(int k) {
  volatile int n = -k;
  int a[n];
  return (int)sizeof a;
}
