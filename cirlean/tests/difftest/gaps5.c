/* fputs and fwrite to stderr (output is not modelled; glibc's results), ffs / ffsl, ungetc and
   fscanf on stdin (at its end: /dev/null natively), lrand48 / seed48 (glibc's drand48 generator)
   (run with CASES=gaps5_cases.txt; a C source). Expected result (labelled per case in the cases
   file): MATCH, or UB from cirrun on the u_ cases (fwrite past the end of its object; a character
   pushed back onto stdin, which is not modelled). */
#include <stdio.h>
#include <stdlib.h>
#include <strings.h>

/* the runner reads the result from the native output, so what these write must not show: an empty
   string, null bytes (which the runner's shell drops) */
int t_fputs(int k) {
  return fputs("", stderr) * 100 + fputs("", stdout) * 10 + k;
}
int t_fwrite(int k) {
  char z[8] = {0};
  return (int) fwrite(z, 1, 5 + k, stderr);
}
int t_fwrite_zero(int k) {
  char buf[2];
  return (int) fwrite(buf, 0, 4, stderr) * 10 + (int) fwrite(buf, 2, 0, stdout) + k;
}
/* undefined: the bytes run past the object */
int u_fwrite_past(int k) {
  char z[4] = {0};
  return (int) fwrite(z, 1, 8, stderr) + k;
}
int t_ffs(int k) {
  return ffs(0) * 1000000 + ffs(1) * 10000 + ffs(1024 << k) * 100 + ffs(-2147483647 - 1);
}
int t_ffsl(int k) {
  return ffsl(1L << (40 + k)) * 100 + ffsl(0) * 10 + ffsl(-1L);
}
int t_ungetc_eof(int k) {
  return ungetc(EOF, stdin) * 10 + getchar() + k;
}
/* undefined here: a character pushed back onto stdin is not modelled */
int u_ungetc_char(int k) {
  return ungetc('a' + k, stdin);
}
int t_fscanf_stdin(int k) {
  int x = 5;
  int r = fscanf(stdin, "%d", &x);
  return r * 100 + x + k;
}
int t_lrand48(int k) {
  unsigned short s[3] = {0x330e, (unsigned short) (1 + k), 2};
  seed48(s);
  long a = lrand48();
  long b = lrand48();
  long c = lrand48();
  return (int) ((a ^ (b << 1) ^ (c << 2)) % 1000003);
}
int t_seed48_old(int k) {
  unsigned short s[3] = {1, 2, 3};
  seed48(s);
  unsigned short t[3] = {4, 5, (unsigned short) (6 + k)};
  unsigned short *o = seed48(t);
  long a = lrand48();
  return o[0] * 10000 + o[1] * 100 + o[2] + (int) (a % 7) * 1000000;
}
