// Floating point: exact printf conversions (%f %e %g with flags, width,
// precision), integer conversions with flags, sscanf, strtod, conversions to
// integers, floor/ceil/round/trunc/fmod, float (binary32) rounding and NaN
// comparisons. Strings are compared through a hash.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>

static int hash_str(const char *s) {
  unsigned h = 5381;
  for (; *s; ++s) h = h * 33 + (unsigned char)*s;
  return (int)(h & 0x7fffffff);
}
// a / b * 10^e, rounded at each step as in C
static double make(int a, int b, int e) {
  double d = (double)a / (double)b;
  for (int i = 0; i < e; ++i) d *= 10.0;
  for (int i = 0; i > e; --i) d /= 10.0;
  return d;
}
static const char *ffmts[] = {
  "%.15g", "%.17g", "%g", "%e", "%.3e", "%f", "%.0f", "%#g", "%10.4f", "%-12.3e|",
  "%+.2f", "% .5g", "%#.3g", "%.0g", "%#.0e", "%E", "%G", "%08.3f", "%-8g|", "%.30g",
  "%1.15g", "%1.17g"};
int t_ffmt(int a, int b, int e, int k) {
  char buf[512];
  double d = make(a, b, e);
  int n = sprintf(buf, ffmts[k], d);
  return hash_str(buf) ^ n;
}
int t_ffmt_inf(int neg, int k) {
  char buf[64];
  double d = 1e308;
  d = d * 10.0;
  if (neg) d = -d;
  int n = sprintf(buf, ffmts[k], d);
  return hash_str(buf) ^ n;
}
static const char *ifmts[] = {
  "%5d", "%-5d|", "%05d", "%+d", "% d", "%.3d", "%08.3d", "%x", "%#x", "%#o",
  "%o", "%X", "%#X", "%hhd", "%hd", "%u", "%.0d", "%-+6d|", "%+05d", "%#5x"};
int t_ifmt(int x, int k) {
  char buf[64];
  int n = sprintf(buf, ifmts[k], x);
  return hash_str(buf) ^ n;
}
int t_ifmt_star(int w, int p, int x) {
  char buf[128];
  int n = sprintf(buf, "[%*d|%-*d|%.*d|%*.*d]", w, x, w, x, p, x, w, p, x);
  return hash_str(buf) ^ n;
}
int t_snprintf(int a, int size) {
  char buf[32];
  memset(buf, 'x', sizeof buf);
  buf[31] = 0;
  int n = snprintf(buf, (size_t)size, "%d-%s", a, "abcdef");
  return hash_str(buf) / 64 * 37 + n;
}
// cJSON's print_number: %1.15g, read back, else %1.17g
int t_print_number(int a, int b, int e) {
  char buf[26];
  double d = make(a, b, e);
  double test = 0.0;
  int length = sprintf(buf, "%1.15g", d);
  if (sscanf(buf, "%lg", &test) != 1 || test != d) length = sprintf(buf, "%1.17g", d);
  return hash_str(buf) ^ length;
}
static const char *inputs[] = {
  "1e+", "1e", "1.5e-3x", "  2", "", "   ", "x", ".", "-", "+.e1", ".5", "5.", "0x1p3", "0x",
  "0x1.8", "inf", "infx", "infin", "INFINITY!", "nan", "nan(123)", "nan(", "1e400", "1e-400",
  "4.9e-324", "2.4703282292062327e-324", "1,5", "--1", "0e", "00012", "1.7976931348623157e308",
  "1.7976931348623159e308", "123456789012345678901234567890", "0.000001234e+10"};
int t_sscanf(int k) {
  double d = -7.0;
  int n = -9;
  int r = sscanf(inputs[k], "%lg%n", &d, &n);
  int cls = d != d ? 3 : (d > 1e308 ? 4 : (d < -1e308 ? 5 : (d > 1e15 || d < -1e15 ? 6 : 0)));
  long long scaled = cls ? 0 : (long long)(d * 1000.0);
  return r * 100000 + n * 1000 + cls * 100 + (int)(scaled % 97);
}
int t_sscanf_int(int k) {
  static const char *ins[] = {"42", "  -17x", "+5", "abc", "", "2147483647", "12 34", "0012", "-0"};
  int a = -1, b = -1;
  int r = sscanf(ins[k], "%d %d", &a, &b);
  return r * 10000 + a % 1000 * 10 + (b & 7);
}
int t_sscanf_float(int k) {
  float f = -1.0f;
  int r = sscanf(inputs[k], "%f", &f);
  return r * 1000 + (f != f ? 999 : (f > 1e9f || f < -1e9f ? 998 : (int)(f * 10.0f) % 997));
}
int t_strtod(int k) {
  char *end;
  double d = strtod(inputs[k], &end);
  int used = (int)(end - inputs[k]);
  int cls = d != d ? 3 : (d > 1e308 ? 4 : (d < -1e308 ? 5 : (d > 1e15 || d < -1e15 ? 6 : 0)));
  long long scaled = cls ? 0 : (long long)(d * 1000.0);
  return used * 1000 + cls * 100 + (int)(scaled % 97);
}
int t_strtof(int k) {
  char *end;
  float f = strtof(inputs[k], &end);
  int used = (int)(end - inputs[k]);
  return used * 1000 + (f != f ? 999 : (f > 1e9f || f < -1e9f ? 998 : (int)(f * 10.0f) % 997));
}
int t_round(int a, int b) {
  double d = (double)a / (double)b;
  int r = (int)floor(d) * 1 + (int)ceil(d) * 10 + (int)round(d) * 100 + (int)trunc(d) * 1000;
  double m = fmod((double)a, (double)b);
  return r + (int)(m * 7.0);
}
int t_negzero(int a) {
  char buf[64];
  double d = ceil(-0.5) + (double)a * 0.0;   // -0 when a = 0
  sprintf(buf, "%g %g %g", d, floor(-0.0), trunc(-0.7));
  return hash_str(buf);
}
int t_to_int(int a, int b) {
  double d = (double)a / (double)b * 1000.0;
  int i = (int)d;
  unsigned char c = (unsigned char)(d / 100.0 + 128.0);
  return i + c;
}
int t_float32(int a, int b) {
  float f = (float)a / (float)b;
  float g = f * 3.0f + 0.1f;
  double d = g;
  float h = (float)(16777217 + a);   // rounded to binary32
  return (int)(d * 1000000.0) % 100003 + ((int)h & 255) * 100000;
}
int t_nan_cmp(int a) {
  double z = (double)a - (double)a;
  double n = z / z;
  return (n == n) + 2 * (n != n) + 4 * (n < 1.0) + 8 * (n >= n) + 16 * (z == -z) + 32 * (n > 0.0);
}
int t_int_to_float(int a, int b) {
  long long big = (long long)a * 1000003 * 1000003 + b;
  double d = (double)big;
  float f = (float)big;
  return (int)(fmod(d, 1000.0)) + (int)(fmod((double)f, 977.0)) * 1000;
}

// sign bits: std::signbit and the isinf-with-sign pattern (cir.signbit)
int t_signbit(int a, int b) {
  double x = (double)a - 0.5;
  double nz = -0.0;
  double ninf = -__builtin_inf();
  int r = 0;
  if (__builtin_signbit(x)) r += 1;
  if (__builtin_signbit(nz)) r += 2;
  if (__builtin_isinf_sign(ninf) == -1) r += 4;
  if (__builtin_isinf_sign(-ninf) == 1) r += 8;
  if (__builtin_isinf_sign(x) == 0) r += 16;
  if (!__builtin_signbit((double)b + 1.0)) r += 32;
  return r;
}

// FP constants that clang prints as hexadecimal bit patterns in CIR (inf,
// nan, -inf of each format; FLT_MAX; long double 0.1)
int t_fp_consts(int a, int b) {
  float fi = __builtin_inff();
  double di = __builtin_inf();
  long double li = __builtin_infl();
  float fn = __builtin_nanf("");
  int r = 0;
  if (fi > 1e30f) r += 1;
  if (di > 1e300) r += 2;
  if (li > 1e300L) r += 4;
  if (fn != fn) r += 8;
  long double x = 0.1L;
  if (x > 0.09L && x < 0.11L) r += 16;
  float y = 3.4028234e38f;
  if (y > 3.0e38f) r += 32;
  float m = -__builtin_inff();
  if (m < -1e30f) r += 64;
  return r + a + b;
}
