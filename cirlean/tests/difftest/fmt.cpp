// printf and scanf families against glibc (C11 7.21.6): fprintf conversions
// d i o u x X c s p n % a A e E f F g G with flags, width and precision
// (digits or *), length modifiers hh h l ll j z t L, snprintf truncation and
// return values, vsprintf/vsnprintf, and sscanf directives (7.21.6.2).
// t_* cases are defined by C11; where C leaves the text to the implementation
// (%p, the leading digit of %a, nan) the expected text is glibc's. ub_* cases
// are undefined behaviour (reason at each) and are not expected to match.
// Strings are compared through a digest of the bytes and the return value.
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cfloat>
#include <climits>

static int digest(const char *s, int len, int n) {
  unsigned h = 5381;
  for (int i = 0; i < len; ++i) h = h * 33 + (unsigned char)s[i];
  return (int)(h % 1000003u) * 1000 + (n < 0 ? 999 : n % 1000);
}
static int dstr(const char *s, int n) { return digest(s, (int)strlen(s), n); }

// integer conversions (7.21.6.1p6-8): zero value with zero precision gives no
// digits; # with o forces a leading 0 and with x prefixes nonzero values; -
// overrides 0, + overrides space, a precision turns 0 off; hh and h convert
// the promoted argument; l ll j z t; %%; * with a negative width is the -
// flag, a negative precision is as if omitted
static int r_int(int k, char *b) {
  switch (k) {
  case 0: return sprintf(b, "%i|%+i|% i|%+i", -42, 42, 42, 0);
  case 1: return sprintf(b, "[%.0d|%.0x|%.0o|%5.0d|%-3.0u]", 0, 0u, 0u, 0, 0u);
  case 2: return sprintf(b, "[%#.0o|%#.0x|%#x|%#o|%#X]", 0u, 0u, 0u, 0u, 0u);
  case 3: return sprintf(b, "[%#.3o|%#o|%#.5x|%#08x|%#-8x|%#10.4X]", 8u, 8u, 255u, 255u, 255u, 255u);
  case 4: return sprintf(b, "[%-08d|%+ d|% 05d|%+.3d|%-+8.3d|%010.4x]", 42, 42, 42, 7, -7, 255u);
  case 5: return sprintf(b, "[%hhd|%hhu|%hhx|%hd|%hu|%hhd]", 200, -1, 0x1234, 40000, -1, -129);
  case 6: return sprintf(b, "[%ld|%lu|%lx|%li]", LONG_MIN, ULONG_MAX, 0xfedcba9876543210ul, LONG_MAX);
  case 7: return sprintf(b, "[%lld|%llu|%#llo|%llX]", LLONG_MIN, ULLONG_MAX, ULLONG_MAX, 0xdeadbeefcafef00dull);
  case 8:
    return sprintf(b, "[%jd|%ju|%zu|%zd|%td|%tx]", INTMAX_MIN, UINTMAX_MAX, (size_t)-1, (ptrdiff_t)-5,
                   (ptrdiff_t)-123456789012LL, (size_t)255);
  case 9: return sprintf(b, "%%|100%%|%d%%|%5d%%", 50, 7);
  case 10: return sprintf(b, "[%40d|%-25u|%.20d|%.20x]", -1, 4000000000u, -42, 0xabcu);
  case 11: return sprintf(b, "[%*d|%.*d|%*.*x|%-*d]", -6, 42, -3, 42, -8, -1, 255u, 4, 9);
  }
  return -2;
}
int t_int(int k) {
  char b[256];
  b[0] = 0;
  int n = r_int(k, b);
  return dstr(b, n);
}

// %c writes its int argument converted to unsigned char (a NUL byte is
// written and counted); %s with a precision writes at most that many bytes
// and needs no terminator within them (7.21.6.1p8)
static int r_chr(int k, char *b) {
  switch (k) {
  case 0: return sprintf(b, "[%c|%3c|%-3c|%c]", 'A', 'B', 'C', 256 + 'D');
  case 1: return sprintf(b, "a%cb", 0);
  case 2: return sprintf(b, "%c%5c|", -1, 0);
  case 3: return sprintf(b, "[%s|%.3s|%10.2s|%-6s|%.0s|%5s]", "hello", "hello", "hello", "ab", "xyz", "");
  case 4: return sprintf(b, "[%.*s|%.*s|%*s|%-*.*s]", 2, "hello", -1, "hello", -5, "ab", 6, 3, "abcdef");
  case 5: {
    char a[3] = {'a', 'b', 'c'};
    return sprintf(b, "[%.3s|%.2s|%-5.3s]", a, a, a);
  }
  case 6: {
    char a[5] = {'w', 'x', 0, 'y', 'z'};
    return sprintf(b, "[%.5s|%s|%.1s]", a, a, a + 3);
  }
  case 7: return sprintf(b, "%s", "");
  }
  return -2;
}
int t_chr(int k) {
  char b[64];
  memset(b, '#', sizeof b);
  int n = r_chr(k, b);
  return digest(b, n < 0 ? 0 : n + 1, n);
}

// %p (7.21.6.1p8, implementation-defined text; glibc: (nil) for a null
// pointer, else 0x and lowercase hex digits)
static int r_ptr(int k, char *b) {
  switch (k) {
  case 0: return sprintf(b, "%p", (void *)0);
  case 1: return sprintf(b, "[%10p|%-10p]", (void *)0, (void *)0);
  case 2: return sprintf(b, "[%p|%20p]", (void *)(uintptr_t)0x1234, (void *)(uintptr_t)0xdeadbeef);
  }
  return -2;
}
int t_ptr(int k) {
  char b[64];
  b[0] = 0;
  int n = r_ptr(k, b);
  return dstr(b, n);
}
// %p of an object's address: the shape of the text only
int t_ptr_obj(int k) {
  char b[64];
  int x = k;
  int n = sprintf(b, "%p", (void *)&x);
  int hex = 1;
  for (int i = 2; i < n; ++i) hex &= (b[i] >= '0' && b[i] <= '9') || (b[i] >= 'a' && b[i] <= 'f');
  return (b[0] == '0') + 2 * (b[1] == 'x') + 4 * (n >= 3) + 8 * (n == (int)strlen(b)) + 16 * hex;
}

// %n stores the number of characters written so far (7.21.6.1p8), also
// through hh, h and ll
int t_cnt(int k) {
  char b[64];
  if (k == 0) {
    int c1 = -1, c2 = -1;
    int n = sprintf(b, "abc%n%5d%n|", &c1, 42, &c2);
    return (c1 * 100 + c2) * 1000 + n;
  }
  signed char sc = -1;
  short sh = -1;
  long long ll = -1;
  int n = sprintf(b, "%s%hhn%hn-%lln", "xyzw", &sc, &sh, &ll);
  return n * 1000000 + sc * 10000 + sh * 100 + (int)ll;
}

// %a and %A (7.21.6.1p8): the exact value in hexadecimal, rounded at a given
// precision, # keeps the point, 0 pads after 0x, infinities; the digit
// before the point of a normalized value is unspecified by C (glibc: 1)
static int r_hexf(int k, char *b) {
  double inf = __builtin_inf(), third = 1.0 / 3.0;
  switch (k) {
  case 0: return sprintf(b, "[%a|%a|%a|%a]", 1.0, 0.5, -3.0, 0.1);
  case 1: return sprintf(b, "[%A|%A|%a]", 255.5, -0.0, 0.0);
  case 2: return sprintf(b, "[%.0a|%.1a|%.2a|%#.0a|%.3a]", 1.5, 1.03125, 1.0, 1.0, third);
  case 3: return sprintf(b, "[%a|%a]", DBL_MAX, DBL_MIN);
  case 4: return sprintf(b, "[%a|%a]", DBL_TRUE_MIN, DBL_TRUE_MIN * 16.0);
  case 5: return sprintf(b, "[%12a|%-12a|%012a|%+a|% a]", 1.0, 1.0, 1.0, 1.0, 2.0);
  case 6: return sprintf(b, "[%a|%A|%5a|%.13a]", inf, -inf, inf, 0.1);
  }
  return -2;
}
int t_hexf(int k) {
  char b[128];
  b[0] = 0;
  int n = r_hexf(k, b);
  return dstr(b, n);
}

// %f %e %g %F %E %G (7.21.6.1p8): infinities ignore the 0 flag; exponents of
// three digits; ties on exact binary values round to even (0.5, 2.5, 0.25,
// 1.125); other decimal values round by their binary value (0.35, 1.005);
// %g takes its style from the exponent after rounding (9995, 999.5); digits
// far into a value (1e23, 2^-1074 to 1074 places); negative zero; NaN (glibc
// writes nan with its sign); long double (x86-64: 64-bit significand)
static int r_ffx(int k, char *b) {
  double inf = __builtin_inf(), q = __builtin_nan("");
  switch (k) {
  case 0: return sprintf(b, "[%F|%F|%E|%G|%G]", 1.5, inf, 1e-10, 1e-10, 1e20);
  case 1: return sprintf(b, "[%f|%+f|%5.1f|%-6f|%010f|%-010e|%08g]", inf, inf, -inf, inf, inf, inf, -inf);
  case 2: return sprintf(b, "[%e|%e|%.3e|%e]", 1e100, 1e-300, DBL_TRUE_MIN, DBL_MAX);
  case 3: return sprintf(b, "[%.0e|%.0e|%.0f|%.0f|%.0f|%.1f|%.2e]", 2.5, 3.5, 0.5, 1.5, 2.5, 0.25, 1.125);
  case 4: return sprintf(b, "[%.1f|%.2f|%.1f|%.3f|%.20f]", 0.35, 1.005, 0.05, 1.0005, 0.1);
  case 5: return sprintf(b, "[%.0f|%.0f|%.17g|%.17e]", 1e22, 1e23, 1e23, DBL_TRUE_MIN);
  case 6: return sprintf(b, "%f", 1e300);
  case 7: return sprintf(b, "%.1074f", DBL_TRUE_MIN);
  case 8: return sprintf(b, "[%g|%g|%g|%g|%g]", 100000.0, 1000000.0, 0.0001, 0.00001, 123456789.0);
  case 9:
    return sprintf(b, "[%.3g|%.3g|%.2g|%.1g|%#.3g|%#g|%.0g|%#.0g]", 9995.0, 999.5, 0.000095, 0.00095, 1.0, 0.0, 0.0,
                   2.0);
  case 10: return sprintf(b, "[%g|%f|%e|%.0f|%+.0f|%.1f|% g]", -0.0, -0.0, -0.0, -0.4, -0.4, -0.04, -0.0);
  case 11: return sprintf(b, "[%f|%F|%e|%5.2g|%+f|%010e]", q, q, q, q, q, q);
  case 12: return sprintf(b, "[%f|%G]", -q, -q);
  case 13: return sprintf(b, "[%Lf|%.20Lf|%Lg|%.25Lg|%La]", 0.1L, 0.1L, 1e-5L, 1.0L / 3, 1.0L);
  case 14: {
    long double x = 1e300L;
    x = x * x;
    return sprintf(b, "[%Le|%Lg]", x, x);
  }
  }
  return -2;
}
int t_ffx(int k) {
  char b[1200];
  b[0] = 0;
  int n = r_ffx(k, b);
  return dstr(b, n);
}

// snprintf (7.21.6.5): returns the length of the full output; writes at most
// n-1 characters and a terminator; n = 0 writes nothing and s may be null.
// The bytes after the terminator stay as they were.
int t_snp(int k) {
  char b[32];
  memset(b, 'x', sizeof b);
  b[31] = 0;
  int n;
  switch (k) {
  case 0: n = snprintf(b, 0, "%s", "hello world"); break;
  case 1: n = snprintf(b, 1, "%s", "hello world"); break;
  case 2: n = snprintf(b, 2, "%s", "hello world"); break;
  case 3: n = snprintf(b, 11, "%s", "hello world"); break;
  case 4: n = snprintf(b, 12, "%s", "hello world"); break;
  case 5: n = snprintf(b, 4, "%f", 3.14159); break;
  case 6: n = snprintf(b, 3, "%c%c%c%c", 'a', 'b', 'c', 'd'); break;
  case 7: n = snprintf(b, 6, "%5d|%s", -1234, "tail"); break;
  case 8: n = snprintf(b, 8, "%.3e", 123456.0); break;
  case 9: n = snprintf(b, 2, "%%%d", 7); break;
  case 10: return snprintf((char *)0, 0, "%d", 123456);
  default: return -2;
  }
  return digest(b, 32, n);
}

// printf and fprintf return the number of characters transmitted
// (7.21.6.1p14, 7.21.6.3p3); only empty output keeps the driver's line
int t_prn(int k) {
  if (k == 0) return printf("%.0s%.0d", "abc", 0) + 10;
  return fprintf(stderr, "%s", "") + 20;
}

// vsprintf and vsnprintf (7.21.6.13, 7.21.6.12) take the arguments as a va_list
static int vsp(char *b, const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int r = vsprintf(b, f, ap);
  va_end(ap);
  return r;
}
static int vsnp(char *b, size_t n, const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  int r = vsnprintf(b, n, f, ap);
  va_end(ap);
  return r;
}
int t_vsn(int k) {
  char b[32];
  memset(b, 'x', sizeof b);
  b[31] = 0;
  int n = k == 0 ? vsp(b, "%d|%s|%.2f", 7, "ab", 2.5) : vsnp(b, 4, "%x-%c", 0xabcdu, 'q');
  return digest(b, 32, n);
}

// undefined behaviour in fprintf, not expected to match: 0 %d with a double
// argument (7.21.6.1p9); 1 %s with a null pointer (p8: a pointer to an array);
// 2 %5% (p8: the complete specification shall be %%); 3 # with d (p6); 4 a
// precision with c (p4); 5 too few arguments (p2); 6 sprintf from an
// overlapping object (7.21.6.6p2)
int ub_fmt(int k) {
  char b[64];
  b[0] = 0;
  int n = -2;
  switch (k) {
  case 0: n = sprintf(b, "%d", 1.5); break;
  case 1: n = sprintf(b, "%s", (const char *)0); break;
  case 2: n = sprintf(b, "%5%"); break;
  case 3: n = sprintf(b, "%#d", 5); break;
  case 4: n = sprintf(b, "%.3c", 'a'); break;
  case 5: n = sprintf(b, "%d %d", 1); break;
  case 6:
    strcpy(b, "ab");
    n = sprintf(b, "%s!", b);
    break;
  }
  return dstr(b, n);
}

// sscanf (7.21.6.2): %i takes the base from the prefix (an input item that is
// only a prefix of a number fails); %o %x; %s, %c and scansets (%c and %[ do
// not skip white space, a ] first in the scanlist is literal); * suppresses
// the assignment; a width limits the item; %% and literal characters; a white
// space directive matches any amount, also none; EOF only for an input
// failure before the first conversion; %n counts without converting; length
// modifiers; floating items in hex, inf and nan spellings, with a width
static int h6(const char *s, int len) {
  unsigned h = 5381;
  for (int i = 0; i < len; ++i) h = h * 33 + (unsigned char)s[i];
  return (int)(h % 1000000u);
}
int t_scn(int k) {
  int a = -1, b = -1, c = -1, n = -1;
  unsigned ua = 7, ub = 7, uc = 7;
  char s1[16], s2[16];
  memset(s1, '#', sizeof s1);
  memset(s2, '#', sizeof s2);
  switch (k) {
  case 0: {
    int r = sscanf("0x1A -012 0", "%i %i %i", &a, &b, &c);
    return r * 1000000 + a * 1000 + (b + 100) * 10 + c;
  }
  case 1: {
    int r = sscanf("08", "%i%n", &a, &n);
    return r * 1000 + a * 10 + n;
  }
  case 2: {
    int r = sscanf("777 0X1f ff", "%o %x %X", &ua, &ub, &uc);
    return r * 100000000 + (int)ua * 100000 + (int)ub * 1000 + (int)uc;
  }
  case 3: {
    int r = sscanf("0x", "%x%n", &ua, &n);
    return (r + 2) * 1000 + (n + 1) * 10 + (int)(ua % 10);
  }
  case 4: {
    int r = sscanf("0x", "%i%n", &a, &n);
    return (r + 2) * 1000 + (n + 1) * 10 + (a + 1);
  }
  case 5: {
    int r = sscanf("  hello world", "%s%n %3s", s1, &n, s2);
    return r * 100000000 + n * 1000000 + (h6(s1, 16) ^ h6(s2, 16)) % 1000000;
  }
  case 6: {
    char c1 = 0, c2 = 0;
    int r1 = sscanf(" x", "%c", &c1);
    int r2 = sscanf(" x", " %c", &c2);
    return (r1 * 10 + r2) * 100000 + c1 * 1000 + c2;
  }
  case 7: {
    int r = sscanf("abcdef", "%3c%n", s1, &n);
    return r * 10000000 + n * 1000000 + h6(s1, 16);
  }
  case 8: {
    int r = sscanf("abcabxyz", "%[abc]%n", s1, &n);
    return r * 10000000 + n * 1000000 + h6(s1, 16);
  }
  case 9: {
    int r = sscanf("abc,def", "%[^,],%s", s1, s2);
    return r * 10000000 + (h6(s1, 16) ^ h6(s2, 16)) % 1000000;
  }
  case 10: {
    int r = sscanf("]x]y", "%[]x]%n", s1, &n);
    return r * 10000000 + n * 1000000 + h6(s1, 16);
  }
  case 11: {
    int r = sscanf("12 34", "%*d %d", &a);
    return r * 1000 + a;
  }
  case 12: {
    int r = sscanf("1234567", "%3d%d", &a, &b);
    return r * 100000000 + a * 100000 + b;
  }
  case 13: {
    int r1 = sscanf("50%", "%d%%", &a);
    int r2 = sscanf("50", "%d%%", &b);
    int r3 = sscanf("5%6", "%d%%%d", &c, &n);
    return (r1 * 100 + r2 * 10 + r3) * 10000 + a * 100 + c * 10 + n;
  }
  case 14: {
    int n1 = -1, n2 = -1;
    int r = sscanf("a   b", "a%n b%n", &n1, &n2);
    int r2 = sscanf("ab", "a b%n", &n);
    return (r + 2) * 100000 + (r2 + 2) * 10000 + (n1 + 1) * 1000 + (n2 + 1) * 10 + (n + 1);
  }
  case 15: {
    int r1 = sscanf("", "%d", &a);
    int r2 = sscanf("   ", "%d", &a);
    int r3 = sscanf("x", "%d", &a);
    int r4 = sscanf("", "%n", &n);
    return (r1 + 2) * 10000 + (r2 + 2) * 1000 + (r3 + 2) * 100 + (r4 + 2) * 10 + (n + 1);
  }
  case 16: {
    int r = sscanf("1-2", "%d+%d", &a, &b);
    return r * 100 + a * 10 + (b == -1);
  }
  case 17: {
    int r = sscanf("  42abc", "%d%n", &a, &n);
    return r * 10000 + a * 100 + n;
  }
  case 18: {
    signed char sc = 0;
    unsigned char uch = 0;
    short sh = 0;
    long long ll = 0;
    unsigned long long ull = 0;
    int r = sscanf("-5 255 -32768 -9223372036854775808 18446744073709551615", "%hhd %hhu %hd %lld %llu", &sc, &uch,
                   &sh, &ll, &ull);
    return r * 100000000 + (sc + 100) * 100000 + uch * 100 + (sh == -32768) * 10 + (ll == LLONG_MIN) * 4 +
           (ull == ULLONG_MAX) * 2;
  }
  case 19: {
    double d1 = 0, d2 = 0, d3 = 0;
    int r = sscanf("0x1.8p1 infinity -nan", "%la %lf %lf", &d1, &d2, &d3);
    return r * 1000 + (d1 == 3.0) * 100 + (d2 > DBL_MAX) * 10 + (d3 != d3);
  }
  case 20: {
    double d = 0;
    int r = sscanf("3.14159", "%4lf%n", &d, &n);
    return r * 100000 + n * 10000 + (int)(d * 1000.0 + 0.5);
  }
  case 21: {
    double d = 0, e = 0;
    int r = sscanf("1e5x 0x1p-2", "%lf%n x%lf", &d, &n, &e);
    return r * 1000000 + n * 100000 + (int)(d / 1000.0) * 100 + (int)(e * 100.0);
  }
  }
  return -2;
}

// undefined behaviour in fscanf, not expected to match: 0 a converted value
// that int cannot represent (7.21.6.2p10); 1 %f with a pointer to double
// (p11-12: pointer to float); 2 %u of "-1", whose value ULONG_MAX does not fit
// in unsigned int (p10)
int ub_scn(int k) {
  int a = -1;
  unsigned u = 7;
  double d = 0;
  int r = -2;
  switch (k) {
  case 0: r = sscanf("99999999999", "%d", &a); return r * 100 + (a & 63);
  case 1: r = sscanf("7.5", "%f", &d); return r * 100 + (d != 0);
  case 2: r = sscanf("-1", "%u", &u); return r * 100 + (int)(u % 97);
  }
  return r;
}
