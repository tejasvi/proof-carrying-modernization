/* Inline asm with memory operands and strncpy / strcat / strrchr (run with CASES=gaps1_cases.txt; a C source).
   An empty template (or nop) leaves its operands as they are: "+g"(x) writes x back, "+m"(x) leaves x,
   "=g"(x) : "0"(v) gives x the value v; the template "movl %0, %1" with a register input and a memory
   input stores the first into the second. Expected result (labelled per case in the cases file): MATCH,
   or UB from cirrun on the u_ cases and the g_ gap. */
#include <string.h>

int a_plus_g_int(int k) {
  int u = 5 + k;
  __asm__("" : "+g"(u));
  return u;
}
int a_plus_g_ptr(int k) {
  char buf[4] = {'a', 'b', 'c', 0};
  char *p = buf + k;
  __asm__("" : "+g"(p));
  return p[0];
}
int a_plus_m(int k) {
  int x = 3, y = 4 + k;
  __asm__ __volatile__("" : "+m"(x), "+m"(y));
  return x * 10 + y;
}
int a_eq_g_tied(int k) {
  int x;
  __asm__("" : "=g"(x) : "0"(7 + k));
  return x;
}
int a_plus_g_two(int k) {
  long a = 2, b = 3 + k;
  __asm__("" : "+g"(a), "+g"(b));
  return (int) (a * 10 + b);
}
int a_nop_input(int k) {
  __asm__ __volatile__("nop" : : "S"(k));
  return k + 1;
}
int a_movl(int k) {
  int v = 0;
  __asm__ __volatile__("movl %0, %1" : : "r"(k + 9), "m"(v));
  return v;
}
/* gap: an empty template that turns a pointer into an int (the pointer's bytes are not modelled) */
int g_ptr_into_int(int k) {
  unsigned x;
  __asm__("" : "=g"(x) : "0"(&x));
  return (int) (x & 0) + k;
}

int s_strncpy_pad(int k) {
  char d[8] = {'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x'};
  strncpy(d, "ab", 6);
  return d[0] * 1000 + d[1] * 10 + d[2] + d[5] + (d[6] == 'x') * 100000 + k;
}
int s_strncpy_cut(int k) {
  char d[4] = {'x', 'x', 'x', 'x'};
  strncpy(d, "abcdef", 3);
  return d[0] + d[2] + (d[3] == 'x') * 1000 + k;
}
int s_strncpy_zero(int k) {
  char d[2] = {'x', 0};
  strncpy(d, "abc", 0);
  return d[0] + k;
}
int s_strncpy_ret(int k) {
  char d[6];
  return (strncpy(d, "hi", 6) == d) + d[1] + k;
}
int s_strcat(int k) {
  char d[10] = "ab";
  strcat(d, "cde");
  return (int) strlen(d) * 1000 + d[2] + d[4] + d[5] + k;
}
int s_strcat_empty(int k) {
  char d[4] = "xy";
  strcat(d, "");
  return (int) strlen(d) + (strcat(d, "z") == d) * 10 + d[2] + k;
}
int s_strrchr(int k) {
  const char s[] = "abcabc";
  return (int) (strrchr(s, 'b' + k) - s) * 10 + (int) (strrchr(s, 0) - s);
}
int s_strrchr_none(int k) {
  char s[] = "abc";
  return (strrchr(s, 'z') == 0) * 10 + (strrchr(s, 'a') == s) + k;
}
/* undefined: the destination is shorter than n */
int u_strncpy_short(int k) {
  char d[3];
  strncpy(d, "abcdef", 5);
  return d[0] + k;
}
/* undefined: the source and the destination overlap */
int u_strncpy_overlap(int k) {
  char d[8] = "abcdef";
  strncpy(d + 1, d, 4);
  return d[1] + k;
}
/* undefined: the destination array is too short for the concatenation */
int u_strcat_short(int k) {
  char d[4] = "ab";
  strcat(d, "cde");
  return d[0] + k;
}
/* undefined: the source and the destination overlap */
int u_strcat_overlap(int k) {
  char d[16] = "abc";
  strcat(d, d + 1);
  return d[3] + k;
}
