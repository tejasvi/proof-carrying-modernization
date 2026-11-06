// vprintf, vfprintf, vsprintf and vsnprintf from a va_list (C11 7.21.6.8-13), the va_list after
// them (indeterminate: 7.21.6.8p2 and its footnote) and scanf on the empty standard input
// (7.21.6.4p3) (CASES=vprintf_cases.txt). The cases labelled UB break those rules (natively they do
// something); the controls keep them.
#include <cstdarg>
#include <cstdio>

// a short digest of a C string (its characters, in order)
static int digest(const char *s) {
  unsigned h = 7;
  for (; *s; ++s) h = h * 31u + (unsigned char)*s;
  return (int)(h % 1000u);
}

// --- vsprintf / vsnprintf through variadic wrappers, each argument with the type its conversion
// needs after the default argument promotions; va_end after the call
static int fmt_into(char *buf, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int n = vsprintf(buf, fmt, ap);
  va_end(ap);
  return n;
}
int t_vsprintf_ok(int k) {
  char buf[96];
  int n = fmt_into(buf, "%d-%s-%u-%ld-%c-%x|%5.2f|%lu|%hhu", k, "ab", 7u, 123456789012L, 'z', 255, 2.5,
                   (unsigned long)k, (unsigned char)200);
  return n * 1000 + digest(buf);
}

// a * field width, %% and a left-justified string
int t_vsprintf_star(int k) {
  char buf[32];
  int n = fmt_into(buf, "%*d%%|%-4s|", 5, k, "ab");
  return n * 1000 + digest(buf);
}

// %u with an int that fits
int t_vsprintf_u_pos(int k) {
  char buf[16];
  int n = fmt_into(buf, "%u", k);
  return n * 1000 + digest(buf);
}

// vsnprintf: at most size - 1 characters and the terminator; the full length is returned
static int nfmt_into(char *buf, int size, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int n = vsnprintf(buf, size, fmt, ap);
  va_end(ap);
  return n;
}
int t_vsnprintf_trunc(int k) {
  char buf[8];
  int n = nfmt_into(buf, sizeof buf, "%d:%s", k, "hello world");
  return n * 1000 + digest(buf);
}

// the length first (vsnprintf without a buffer), then va_start again after va_end for the text,
// as Thrift's TOutput::printf does
static int two_pass(char *out, int cap, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int need = vsnprintf(nullptr, 0, fmt, ap);
  va_end(ap);
  if (need >= cap) return -1;
  va_start(ap, fmt);
  int n = vsnprintf(out, need + 1, fmt, ap);
  va_end(ap);
  return n == need ? n : -2;
}
int t_vsnprintf_two_pass(int k) {
  char buf[32];
  int n = two_pass(buf, sizeof buf, "[%d|%s|%c]", k, "xy", 'q');
  return n * 1000 + digest(buf);
}

// a va_copy for the length, the original for the text
static int copy_first(char *out, const char *fmt, ...) {
  va_list ap, cp;
  va_start(ap, fmt);
  va_copy(cp, ap);
  int need = vsnprintf(nullptr, 0, fmt, cp);
  va_end(cp);
  int n = vsprintf(out, fmt, ap);
  va_end(ap);
  return n == need ? n : -1;
}
int t_vcopy_ok(int k) {
  char buf[32];
  int n = copy_first(buf, "%x.%o", k, k);
  return n * 1000 + digest(buf);
}

// the arguments after the owner's va_arg, through a function with a va_list parameter
static int vfmt(char *out, const char *fmt, va_list ap) { return vsprintf(out, fmt, ap); }
static int skip_first(char *out, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int first = va_arg(ap, int);
  int n = vfmt(out, fmt, ap);
  va_end(ap);
  return first * 100 + n;
}
int t_vlist_rest(int k) {
  char buf[32];
  int r = skip_first(buf, "%d/%d", 9, k, k + 1);
  return r * 1000 + digest(buf);
}

// --- vprintf / vfprintf: standard output and error carry the result, so formats that print
// nothing (%.0s, and %.0d or %.0u of 0)
static int print_nothing(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int n = vprintf(fmt, ap);
  va_end(ap);
  return n;
}
static int eprint_nothing(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int n = vfprintf(stderr, fmt, ap);
  va_end(ap);
  return n;
}
int t_vprintf_ok(int k) { return print_nothing("%.0s%.0d", "text", 0) + eprint_nothing("%.0s%.0u", "x", 0u) + k; }

// --- scanf on the empty standard input: EOF before the first conversion (the object keeps its
// value), 0 for a format of white space only
int t_scanf_eof(int k) {
  int x = k;
  int r = scanf("%d", &x);
  return r * 100 + x;
}
int t_scanf_space(int k) { return scanf(" ") * 100 + k; }

// --- UB: an argument of another type than its conversion needs (7.21.6.1p9)
int t_ub_vsprintf_d_long(int k) {
  char buf[32];
  int n = fmt_into(buf, "%d", (long)k);
  return n * 1000 + digest(buf);
}
int t_ub_vsprintf_ld_int(int k) {
  char buf[32];
  int n = fmt_into(buf, "%ld", k);
  return n * 1000 + digest(buf);
}
int t_ub_vsprintf_c_long(int k) {
  char buf[32];
  int n = fmt_into(buf, "%c", 64L + k);
  return n * 1000 + digest(buf);
}
// UB: vprintf %.0d with a long (natively it prints nothing)
int t_ub_vprintf_d_long(int k) { return print_nothing("%.0d", 0L) + k; }

// UB: vsnprintf %u with a negative int (its value does not fit unsigned int)
int t_ub_vsnprintf_u_neg(int k) {
  char buf[32];
  int n = nfmt_into(buf, sizeof buf, "%u", -k);
  return n * 1000 + digest(buf);
}

// --- UB: after vsprintf the va_list's value is indeterminate; only va_end may follow
// (7.21.6.8p2 and its footnote, 7.16p3)
static int arg_after(char *out, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int n = vsprintf(out, fmt, ap);
  int x = va_arg(ap, int);
  va_end(ap);
  return n * 100 + x;
}
int t_ub_va_arg_after_vsprintf(int k) {
  char buf[16];
  int r = arg_after(buf, "%d", k, 7);
  return r * 1000 + digest(buf);
}

// UB: a second vsprintf on the va_list without va_end and va_start between them
static int twice_fmt(char *out, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int a = vsprintf(out, fmt, ap);
  int b = vsprintf(out, fmt, ap);
  va_end(ap);
  return a * 10 + b;
}
int t_ub_vsprintf_twice(int k) {
  char buf[16];
  int r = twice_fmt(buf, "%d", k, 8);
  return r * 1000 + digest(buf);
}

// UB: va_copy of the va_list after vsnprintf
static int copy_after(char *out, const char *fmt, ...) {
  va_list ap, cp;
  va_start(ap, fmt);
  int n = vsnprintf(out, 16, fmt, ap);
  va_copy(cp, ap);
  int x = va_arg(cp, int);
  va_end(cp);
  va_end(ap);
  return n * 100 + x;
}
int t_ub_va_copy_after_vsnprintf(int k) {
  char buf[16];
  int r = copy_after(buf, "%d", k, 6);
  return r * 1000 + digest(buf);
}

// UB: va_start again after vsprintf, without va_end (7.16.1.4p3)
static int restart_no_end(char *out, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int a = vsprintf(out, fmt, ap);
  va_start(ap, fmt);
  int b = vsprintf(out, fmt, ap);
  va_end(ap);
  return a * 10 + b;
}
int t_ub_va_start_after_vsprintf(int k) {
  char buf[16];
  int r = restart_no_end(buf, "%d", k);
  return r * 1000 + digest(buf);
}

// UB: a return without va_end after vsprintf (7.16.1.3p2)
static int no_end(char *out, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  return vsprintf(out, fmt, ap);
}
int t_ub_vsprintf_no_va_end(int k) {
  char buf[16];
  int n = no_end(buf, "%d", k);
  return n * 1000 + digest(buf);
}

// UB: vsprintf on a va_list after its va_end (7.21.6.13p2: it shall have been initialized by
// va_start)
static int after_end(char *out, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  va_end(ap);
  return vsprintf(out, fmt, ap);
}
int t_ub_vsprintf_after_va_end(int k) {
  char buf[16];
  int n = after_end(buf, "%d", k);
  return n * 1000 + digest(buf);
}

// --- gaps (cirlean's)
// the owner's vsprintf after a callee's va_arg on its va_list (UB in C11 7.16p3) is not caught: the
// model sees the va_list, not which function calls it
static int first_of(va_list ap) { return va_arg(ap, int); }
static int callee_then_owner(char *out, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int a = first_of(ap);
  int n = vsprintf(out, fmt, ap);
  va_end(ap);
  return a * 100 + n;
}
int t_gap_callee_then_vsprintf(int k) {
  char buf[16];
  int r = callee_then_owner(buf, "%d", 3, k);
  return r * 1000 + digest(buf);
}

// through a function pointer the arguments keep their values only, so a long read by %d is not
// caught (UB in C11 7.21.6.1p9) when its value fits int
static int (*fmt_into_ptr)(char *, const char *, ...) = fmt_into;
int t_gap_vsprintf_fnptr(int k) {
  char buf[16];
  int n = fmt_into_ptr(buf, "%d", (long)k);
  return n * 1000 + digest(buf);
}
