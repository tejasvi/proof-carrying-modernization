/* Library audit items (cjlemmas' FINDINGS: G29, M2, F4, F6, F8), C sources, run with MODE=status
   CASES=libfix2_cases.txt: the exit status is the test function's result (or quick_exit's).
   The audit's tests are t89 (t_cx_fail_stronger), t109 (t_lc_wide), t37 (t_sscanf_lu_neg), t69
   (t_qe_handler) and t108 (t_s_singlechar); the others are controls. Expected result, labelled
   per case in the cases file: MATCH, or UB from cirrun. */
#include <limits.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

/* G29: the failure order of a compare-exchange shall be neither release nor acq_rel and no
   stronger than the success order (C11 7.17.7.4p2; the second rule is not in C23) */
int t_cx_fail_stronger(int k) {
  atomic_int x = 5;
  int e = 5;
  int ok = atomic_compare_exchange_strong_explicit(&x, &e, 9, memory_order_relaxed, memory_order_seq_cst);
  return ok * 100 + atomic_load(&x) + k;
}
int t_cx_orders_ok(int k) {
  atomic_int x = 5;
  int e = 5;
  int ok = atomic_compare_exchange_strong_explicit(&x, &e, 9, memory_order_acq_rel, memory_order_acquire);
  return ok * 100 + atomic_load(&x) + k;
}
int t_cx_default(int k) {
  atomic_int x = 5;
  int e = 6;
  int ok = atomic_compare_exchange_strong(&x, &e, 9);
  return ok * 100 + e * 10 + atomic_load(&x) + k;
}
/* the failure order as a variable: clang's switch picks the order at run time */
int t_cx_var_failure(int k) {
  atomic_int x = 5;
  int e = 5;
  int ok = atomic_compare_exchange_strong_explicit(&x, &e, 9, memory_order_relaxed, (memory_order)k);
  return ok * 100 + atomic_load(&x);
}
/* a release failure order: undefined in C11, but clang turns it into relaxed before the CIR */
int t_cx_fail_release(int k) {
  atomic_int x = 5;
  int e = 5;
  int ok = atomic_compare_exchange_strong_explicit(&x, &e, 9, memory_order_seq_cst, memory_order_release);
  return ok * 100 + atomic_load(&x) + k;
}

/* M2: %lc converts as wcrtomb does (C11 7.21.6.1p8); in the C locale (ASCII in glibc) another
   wide character is an encoding error, and the result is negative (p14, 7.21.6.6p3) */
int t_lc_wide(int k) {
  char buf[16] = "zz";
  return sprintf(buf, "%lc", (wint_t)(0x263A + k));
}
int t_lc_ascii(int k) {
  char buf[16];
  int r = sprintf(buf, "%lc", (wint_t)('A' + k));
  return r * 100 + buf[0];
}
int t_lc_prefix(int k) {
  char buf[8];
  memset(buf, 'z', sizeof buf);
  int r = sprintf(buf, "ab%lcc", (wint_t)(0x80 + k));
  return (r == -1) * 100 + (buf[2] == 0) * 10 + (buf[1] == 'b');
}
int t_lc_snprintf(int k) {
  char buf[8];
  return snprintf(buf, sizeof buf, "%lc", (wint_t)(0xff + k));
}
int t_lc_printf(int k) { return printf("%lc", (wint_t)(0x263A + k)) == -1 ? 77 : 78; }

/* F4: sscanf %u, %x convert as strtoul does (C11 7.21.6.2p12): "-1" is ULONG_MAX */
int t_sscanf_lu_neg(int k) {
  unsigned long ul = 0;
  sscanf("-1", "%lu", &ul);
  return (ul == ULONG_MAX) + k;
}
int t_sscanf_lx_neg(int k) {
  unsigned long ul = 0;
  sscanf("-ff", "%lx", &ul);
  return (ul == 0UL - 0xff) + k;
}
int t_sscanf_lu_neg0(int k) {
  unsigned long ul = 9;
  sscanf("-0", "%lu", &ul);
  return (int)ul + 5 + k;
}
/* ULONG_MAX does not fit an unsigned int (p10: undefined; glibc stores UINT_MAX) */
int t_sscanf_u_neg(int k) {
  unsigned u = 0;
  sscanf("-1", "%u", &u);
  return (u == UINT_MAX) + k;
}

/* F6: quick_exit runs the at_quick_exit handlers, the last registered first, and no atexit
   handler (C11 7.22.4.3, 7.22.4.7) */
static int g_q;
static void h_exit7(void) { _Exit(7); }
int t_qe_handler(int k) {
  at_quick_exit(h_exit7);
  quick_exit(3 + k);
}
static void h_exit_g(void) { _Exit(g_q); }
static void h_set42(void) { g_q = 42; }
int t_qe_order(int k) {
  g_q = 1;
  at_quick_exit(h_exit_g);
  at_quick_exit(h_set42);
  quick_exit(4 + k);
}
static void h_exit9(void) { _Exit(9); }
int t_qe_no_atexit(int k) {
  atexit(h_exit9);
  quick_exit(5 + k);
}
static void h_plain(void) { g_q = 1; }
int t_qe_returns(int k) {
  at_quick_exit(h_plain);
  quick_exit(6 + k);
}
static void h_exit33(void) { _Exit(33); }
static void h_reg33(void) { at_quick_exit(h_exit33); }
int t_qe_registered_during(int k) {
  at_quick_exit(h_reg33);
  quick_exit(8 + k);
}
static void h_calls_exit(void) { exit(1); }
int t_qe_exit_in_handler(int k) {
  at_quick_exit(h_calls_exit);
  quick_exit(2 + k);
}

/* F8: a character object that is no array element acts as an array of one (C11 6.5.6p7) */
int t_s_singlechar(int k) {
  char c = 'x';
  char buf[8];
  int r = sprintf(buf, "%.1s", &c);
  return r * 100 + (buf[0] == 'x') * 10 + (buf[1] == 0) + k;
}
int t_s_singlechar_nul(int k) {
  char c = 0;
  char buf[8];
  return sprintf(buf, "%s", &c) + 10 + k;
}
/* reading past the array of one */
int t_s_singlechar_prec2(int k) {
  char c = 'x';
  char buf[8];
  return sprintf(buf, "%.2s", &c) + k;
}
int t_s_singlechar_unterminated(int k) {
  char c = 'x';
  char buf[8];
  return sprintf(buf, "%s", &c) + k;
}
