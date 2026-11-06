// Cases added with the libcfix model fixes, next to the difftestx cases in
// fmt.cpp and fpx.cpp: %s with a precision on a char array without a
// terminator (C11 7.21.6.1p8) through sprintf, snprintf and printf; %x and %X
// with a 0x prefix (7.21.6.2p12); fmin and fmax (7.12.12.2-3, F.10.9.2-3;
// with libc++ they become cir.fminnum and cir.fmaxnum). t_* cases are
// defined by C11; ub_* cases are undefined behaviour, not expected to match.
#include <cfloat>
#include <cmath>
#include <cstdio>
#include <cstring>

static int digest(const char *s, int len, int n) {
  unsigned h = 5381;
  for (int i = 0; i < len; ++i) h = h * 33 + (unsigned char)s[i];
  return (int)(h % 1000003u) * 1000 + (n < 0 ? 999 : n % 1000);
}

// %s and %.*s with a precision: at most that many characters are read, and
// the array needs no terminator among them; one before them ends the text
int t_sprec(int k) {
  char a[4] = {'a', 'b', 'c', 'd'};
  char c[3] = {'x', 0, 'y'};
  char b[32];
  memset(b, 'x', sizeof b);
  b[31] = 0;
  int n = -2;
  switch (k) {
  case 0: n = sprintf(b, "[%.*s|%-6.*s|%.4s]", 2, a, 4, a, a); break;
  case 1: n = snprintf(b, 3, "%.4s", a); break;
  case 2: n = snprintf(b, 32, "%5.3s|%.*s", a, 0, a); break;
  case 3: return printf("%.0s", a) + 100;
  case 4: n = sprintf(b, "[%.3s|%.1s]", c, c + 2); break;
  }
  return digest(b, 32, n);
}

// a precision beyond the array, with no terminator in it, reads past the
// array: undefined (7.21.6.1p8: the array shall contain a null character)
int ub_sprec(int k) {
  char a[4] = {'a', 'b', 'c', 'd'};
  char b[32];
  b[0] = 0;
  int n = sprintf(b, "%.5s", a);
  return digest(b, (int)strlen(b), n) + k;
}

// %x and %X take an optional 0x or 0X after the sign, as strtoul in base 16;
// 0x alone (also when a width cuts the item there) is only a prefix of a
// number: a matching failure (7.21.6.2p9-10)
int t_scnx(int k) {
  unsigned u = 7, v = 7;
  unsigned long long w = 7;
  int n = -1, r = -2;
  switch (k) {
  case 0: r = sscanf("0x1f", "%x%n", &u, &n); break;
  case 1: r = sscanf("0X1F 0x", "%X %x", &u, &v); break;
  case 2: r = sscanf("+0x7fffffff", "%x%n", &u, &n); break;
  case 3: r = sscanf("0x1f", "%3x%n", &u, &n); break;
  case 4: r = sscanf("0x1f", "%2x", &u); break;
  case 5: r = sscanf("0xffffffffffffffff", "%llx%n", &w, &n); break;
  }
  return (r + 2) * 10000000 + (n + 1) * 100000 + (int)(u % 1000) * 100 + (int)(v % 10) * 10 + (int)(w % 10);
}

// format combinations C11 leaves undefined, not expected to match: # with s,
// c and u (7.21.6.1p6; case 10 through printf, empty natively); a precision
// with c (p4); length modifiers the conversion does not take (p7: h with s,
// h and j with f, L with d, an invalid lll); the 0 flag with s (p6)
int ub_fmtx(int k) {
  char b[64];
  b[0] = 0;
  int n = -2;
  switch (k) {
  case 0: n = sprintf(b, "%#s", "ab"); break;
  case 1: n = sprintf(b, "%#c", 'a'); break;
  case 2: n = sprintf(b, "%#u", 5u); break;
  case 3: n = snprintf(b, sizeof b, "%.2c", 'a'); break;
  case 4: n = sprintf(b, "%hs", "ab"); break;
  case 5: n = sprintf(b, "%hf", 1.5); break;
  case 6: n = sprintf(b, "%jf", 1.5); break;
  case 7: n = sprintf(b, "%Ld", 5LL); break;
  case 8: n = sprintf(b, "%llld", 5LL); break;
  case 9: n = sprintf(b, "%0s", "ab"); break;
  case 10: return printf("%#.0s", "ab") + 100;
  }
  return digest(b, (int)strlen(b), n);
}

// combinations that stay defined: l before a floating conversion has no
// effect (p7); + and space only act on signed conversions (p6); # with o, x
// and the floating conversions; 0 with d after - is ignored
int t_fmtok(int k) {
  char b[64];
  memset(b, 'x', sizeof b);
  b[63] = 0;
  int n = k == 0 ? sprintf(b, "[%lf|%le|%lg|%#lg]", 1.5, 1.5, 1.5, 2.0)
                 : sprintf(b, "[% u|%+u|%+x|%#o|%#.0f|%-05d]", 5u, 5u, 255u, 8u, 3.0, 7);
  return digest(b, 64, n);
}

// fmin and fmax on ordinary values, infinities and subnormals, and the float
// versions with a NaN argument
int t_fminmax(int k) {
  double a = 1.5, b = -2.5, inf = __builtin_inf(), tm = DBL_TRUE_MIN, z = 0.0;
  float fa = 1.5f, fb = -2.5f, fq = __builtin_nanf("");
  if (k == 0)
    return (fmin(a, b) == b) + 2 * (fmax(a, b) == a) + 4 * (fmin(-inf, a) == -inf) + 8 * (fmax(inf, b) == inf) +
           16 * (fmin(tm, z) == z) + 32 * (fmax(-tm, z) == z) + 64 * (fmax(tm, -tm) == tm);
  return (fminf(fa, fb) == fb) + 2 * (fmaxf(fa, fb) == fa) + 4 * (fminf(fq, fb) == fb) + 8 * (fmaxf(fa, fq) == fa) +
         16 * (fminf(fq, fq) != fminf(fq, fq));
}
