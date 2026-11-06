// More library-model checks (cjlemmas' library audit): pointer arguments of
// memcpy, memmove, memset and memcmp must be valid also with length 0 (C11
// 7.24.1p2, 7.1.4p1); sprintf and snprintf must not read the format string or
// a %s argument (with a precision: the characters it reads) from the text they
// write (7.21.6.6p2, 7.21.6.5p2); fprintf's stream must be a valid FILE *
// (7.1.4p1). ub_* cases are undefined, the rest are expected to match.
#include <cstdio>
#include <cstdlib>
#include <cstring>

// a null pointer with length 0
int ub_memcpy_null_src0(int k) {
  char a[4] = {1, 2, 3, 4};
  memcpy(a, (const void *)0, 0);
  return a[0] + k;
}
int ub_memcpy_null_dst0(int k) {
  char a[4] = {1, 2, 3, 4};
  memcpy((void *)0, a, 0);
  return a[1] + k;
}
int ub_memmove_null0(int k) {
  char a[4] = {1, 2, 3, 4};
  memmove((void *)0, a, 0);
  return a[2] + k;
}
int ub_memset_null0(int k) {
  memset((void *)0, 0, 0);
  return 7 + k;
}
// (the length comes from k = 0, as Clang folds memcmp with a constant length 0)
int ub_memcmp_null0(int k) {
  char a[4] = {1, 2, 3, 4};
  return memcmp((const void *)0, a, (size_t)k) + 7 + k;
}
// a dangling pointer (its heap block freed) with length 0
int ub_memcpy_dangling0(int k) {
  char a[4] = {1, 2, 3, 4};
  char *p = (char *)malloc(4);
  free(p);
  memcpy(a, p, 0);
  return a[3] + k;
}
// a string literal as memset's destination (non-modifiable storage), length 0
int ub_memset_literal0(int k) {
  memset((void *)"abc", 0, 0);
  return 7 + k;
}

// length 0 with valid pointers, also one past the end of an array
int t_mem_zero_valid(int k) {
  char a[4] = {1, 2, 3, 4};
  char b[4] = {5, 6, 7, 8};
  memcpy(a, b, 0);
  memmove(b, a, 0);
  memset(a + 4, 9, 0);
  return a[0] * 1000 + b[0] * 100 + memcmp(a, b + 4, (size_t)k) * 10 + 7 + k;
}

// the format string inside the destination
int ub_sprintf_fmt_overlap(int k) {
  char buf[16] = "ab%d";
  sprintf(buf, buf, 5 + k);
  return buf[0];
}
int ub_snprintf_fmt_overlap(int k) {
  char buf[16] = "ab%d";
  snprintf(buf, sizeof buf, buf, 5 + k);
  return buf[0];
}
// a %.3s source without a terminator overlapping the destination
int ub_sprintf_prec_overlap(int k) {
  char buf[8] = {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'};
  sprintf(buf + 1, "%.3s", buf);
  return buf[1] + k;
}
// a %.2s source whose two characters lie before the destination: no overlap,
// although the string runs on into it
int t_sprintf_prec_nooverlap(int k) {
  char buf[16] = "abcdefgh";
  int n = sprintf(buf + 6, "%.2s", buf);
  return n * 1000 + buf[6] * 10 + (buf[8] == 0) + k;
}
// the format in a literal, the destination elsewhere
int t_sprintf_fmt_separate(int k) {
  char buf[16];
  char src[8] = "xy";
  int n = sprintf(buf, "%s-%d", src, 4 + k);
  return n * 1000 + buf[0] + buf[3];
}

// fprintf with a null stream; with stdout and stderr
int ub_fprintf_null_stream(int k) { return fprintf((FILE *)0, "%d", 1 + k); }
int t_fprintf_stderr(int k) { return fprintf(stderr, "%s", "") + fprintf(stdout, "%.0d", 0) + 7 + k; }
int t_std_streams_distinct(int k) {
  return (stdin != 0) + 2 * (stdout != 0) + 4 * (stderr != 0) + 8 * (stdout != stderr) + 16 * (stdin != stdout) + k;
}
// snprintf with n = 0 may take a null destination (7.21.6.5p2)
int t_snprintf_null0(int k) { return snprintf((char *)0, 0, "%d", 123 + k); }
