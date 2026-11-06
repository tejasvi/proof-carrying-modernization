/* va_list life cycle and printf argument types after rog's audit of next3 (CASES=auditva_cases.txt):
   the functions up to v_fnptr_sprintf are rog's (soundaudit_n3: n3va.c, n3b3.c), the ones after it
   this branch's. */
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

/* a pointer to a va_list passed to a callee, which takes one argument; the caller then
   takes the next (7.16p3, footnote 253: permitted) */
static int take_p(va_list *pap) { return va_arg(*pap, int); }
static int sum_p(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = take_p(&ap);
  int b = va_arg(ap, int);
  va_end(ap);
  return a * 10 + b;
}
int v_ptr_to_va_list(int k) { return sum_p(2, 3 + k, 4); }

/* the va_list itself passed to two callees, each taking an argument: after the first, the
   caller's ap is indeterminate and may only be passed to va_end (7.16p3) */
static int take_v(va_list ap) { return va_arg(ap, int); }
static int sum_v(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = take_v(ap);
  int b = take_v(ap);
  va_end(ap);
  return a * 10 + b;
}
int v_two_callees(int k) { return sum_v(2, 3 + k, 4); }

/* va_end in a callee: va_start is not matched by a va_end in the same function (7.16.1p1) */
static void end_v(va_list ap) { va_end(ap); }
static int first_end_in_callee(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = va_arg(ap, int);
  end_v(ap);
  return a;
}
int v_end_in_callee(int k) { return first_end_in_callee(1, 5 + k); }

/* control: va_copy, both lists read independently */
static int copy_both(int n, ...) {
  va_list ap, aq;
  va_start(ap, n);
  va_copy(aq, ap);
  int a = va_arg(aq, int);
  int b = va_arg(aq, int);
  int c = va_arg(ap, int);
  va_end(aq);
  va_end(ap);
  return a * 100 + b * 10 + c;
}
int v_copy_independent(int k) { return copy_both(2, 3 + k, 4); }

/* va_start in an inner block that ends without va_end, then a return (7.16.1p1, 7.16.1.3p2) */
static int va_inner_block(int n, ...) {
  int x;
  {
    va_list ap;
    va_start(ap, n);
    x = va_arg(ap, int);
  }
  return x;
}
int v_block_ends_without_va_end(int k) { return va_inner_block(1, 3 + k); }

/* a mutable char array used as a format, changed before the call: "%s|" (defined) */
static char fmt_s[] = "%d|";
int v_fmt_mutable_defined(int k) {
  char buf[32];
  fmt_s[1] = 's';
  sprintf(buf, fmt_s, k ? "xyz" : "ab");
  return (int)strlen(buf) * 100 + buf[0];
}
/* the same array changed to "%ld" with an int argument (7.21.6.1p9) */
static char fmt_l[8] = "%d";
int v_fmt_mutable_ub(int k) {
  char buf[32];
  fmt_l[1] = 'l';
  fmt_l[2] = 'd';
  fmt_l[3] = 0;
  sprintf(buf, fmt_l, 5 + k);
  return buf[0];
}
/* sprintf through a function pointer, literal format, %ld with an int */
int v_fnptr_sprintf(int k) {
  char buf[32];
  int (*pf)(char *, const char *, ...) = sprintf;
  pf(buf, "%ld", 5 + k);
  return buf[0];
}

/* --- this branch's */
/* a callee goes on with the va_list it was given, two va_args, then the caller ends it */
static int take_two(va_list ap) {
  int a = va_arg(ap, int);
  return a * 10 + va_arg(ap, int);
}
static int callee_twice(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int r = take_two(ap);
  va_end(ap);
  return r;
}
int t_callee_goes_on(int k) { return callee_twice(2, 3 + k, 4); }

/* a callee copies the va_list it advanced and reads from the copy, which it ends */
static int take_copy(va_list ap) {
  int a = va_arg(ap, int);
  va_list aq;
  va_copy(aq, ap);
  int b = va_arg(aq, int);
  va_end(aq);
  return a * 10 + b;
}
static int callee_copies(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int r = take_copy(ap);
  va_end(ap);
  return r;
}
int t_callee_copies(int k) { return callee_copies(2, 3 + k, 4); }

/* va_end through a pointer in a helper: not in the function of the va_start (7.16.1p1) */
static void end_p(va_list *pap) { va_end(*pap); }
static int end_through_pointer(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int a = va_arg(ap, int);
  end_p(&ap);
  return a;
}
int t_end_through_pointer(int k) { return end_through_pointer(1, 5 + k); }

/* a va_list started in a loop body that a break leaves without va_end */
static int break_out(int n, ...) {
  int x = 0;
  for (int i = 0; i < 2; ++i) {
    va_list ap;
    va_start(ap, n);
    x = va_arg(ap, int);
    if (x > 0) break;
    va_end(ap);
  }
  return x;
}
int t_break_without_va_end(int k) { return break_out(1, 3 + k); }

/* the same with continue */
static int continue_on(int n, ...) {
  int x = 0;
  for (int i = 0; i < 2; ++i) {
    va_list ap;
    va_start(ap, n);
    x = x + va_arg(ap, int);
    if (i == 0) continue;
    va_end(ap);
  }
  return x;
}
int t_continue_without_va_end(int k) { return continue_on(1, 3 + k); }

/* a goto out of the block of the va_list, without va_end */
static int goto_out(int n, ...) {
  int x = 0;
  {
    va_list ap;
    va_start(ap, n);
    x = va_arg(ap, int);
    if (x > 0) goto done;
    va_end(ap);
  }
done:
  return x;
}
int t_goto_without_va_end(int k) { return goto_out(1, 3 + k); }

/* control: a va_list ended in its inner block, a goto inside the block, a break after va_end */
static int ended_inside(int n, ...) {
  int x = 0;
  for (int i = 0; i < 3; ++i) {
    va_list ap;
    va_start(ap, n);
    int t = 0;
  again:
    t = t + 1;
    if (t < 2) goto again;
    x = x + va_arg(ap, int) * t;
    va_end(ap);
    if (i == 1) break;
  }
  return x;
}
int t_ended_inside(int k) { return ended_inside(1, 3 + k); }

/* vfprintf with a null stream (7.21.6.8p2, 7.1.4p1), rog's (n3p7.c) */
static int vf_null(const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int r = vfprintf(NULL, f, ap);
  va_end(ap);
  return r;
}
int q_vfprintf_null(int k) { return vf_null("%d\n", k); }
/* control: vfprintf to stderr, a format that prints nothing */
static int vf_stderr(const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int r = vfprintf(stderr, f, ap);
  va_end(ap);
  return r;
}
int t_vfprintf_stderr(int k) { return vf_stderr("%.0d", 0) + k; }
