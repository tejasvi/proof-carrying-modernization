// Floating-point arithmetic, conversions and <math.h> against native x86-64:
// IEC 60559 binary32/binary64 as in C11 Annex F (glibc and gcc define
// __STDC_IEC_559__; floats.cpp also takes 0/0 and overflow as IEEE), long
// double as x87 extended (64-bit significand). The <float.h> limits at work
// (5.2.4.2.2): epsilon, round to nearest even at the edges of each format,
// overflow to infinity, subnormals down to the least subnormal,
// FLT_EVAL_METHOD 0, no contraction of a*b+c; signed zero; conversions
// between integer and floating types (6.3.1.4-5, F.4); the math functions
// cirlean models (7.12) at the special values of F.10. Operands come from
// variables, so neither compiler folds the operations. Results are exact:
// fp_id, or flags read bit by bit. ub_* cases are undefined behaviour, not
// expected to match.
#include <cfloat>
#include <climits>
#include <cmath>
#include <math.h>

// exact identity of a double: NaN, signed zeros (by 1/d, as IEEE), infinities,
// else sign, binary exponent and 52-bit fraction found by exact scaling
static int fp_id(double d) {
  if (d != d) return 1;
  if (d == 0.0) return 1.0 / d < 0.0 ? 4 : 3;
  if (d > DBL_MAX) return 5;
  if (d < -DBL_MAX) return 6;
  unsigned long long s = d < 0.0;
  if (s) d = -d;
  long long e = 0;
  while (d >= 2.0) {
    d *= 0.5;
    ++e;
  }
  while (d < 1.0) {
    d *= 2.0;
    --e;
  }
  unsigned long long m = (unsigned long long)((d - 1.0) * 4503599627370496.0);
  unsigned long long h = m * 0x9E3779B97F4A7C15ull ^ (unsigned long long)(e + 2000) * 0xC2B2AE3D27D4EB4Full ^ s;
  return (int)((h ^ (h >> 32)) % 999983u) + 10;
}
static int mix(int h, int v) { return (int)(((unsigned)h * 31u + (unsigned)v) % 1000003u); }
static int fold(unsigned long long u) { return (int)(u % 9999991ull); }
// the sign bit; signbit itself only for a NaN (t_nan), so the zero cases do
// not depend on cir.signbit
static int sb(double d) {
  if (d != d) return __builtin_signbit(d) != 0;
  return d == 0.0 ? 1.0 / d < 0.0 : d < 0.0;
}

// rounding at the edges of binary64 and binary32: 1 + eps/2 and 1 - eps/4 are
// ties (even: 1); half an ulp above DBL_MAX or FLT_MAX is a tie whose even
// neighbour is 2^1024 or 2^128 (inf); subnormal results are exact or ties
// (the least subnormal halved is 0, times 1.5 and 2.5 is 2 units); x - y is
// 0 only when x == y (gradual underflow); float operations round to float
// (FLT_EVAL_METHOD 0: 1e30f * 1e10f overflows before the division); a*b+c is
// two roundings
int t_lim(int k) {
  double one = 1.0, eps = DBL_EPSILON, M = DBL_MAX, mn = DBL_MIN, tm = DBL_TRUE_MIN;
  float onef = 1.0f, epsf = FLT_EPSILON, Mf = FLT_MAX, mnf = FLT_MIN, tmf = FLT_TRUE_MIN;
  switch (k) {
  case 0:
    return (one + eps > one) + 2 * (one + eps / 2 == one) + 4 * (one + eps * 0.75 == one + eps) +
           8 * (one - eps / 4 == one) + 16 * (one - eps / 2 < one);
  case 1:
    return (onef + epsf > onef) + 2 * (onef + epsf / 2 == onef) + 4 * (onef + epsf * 0.75f == onef + epsf) +
           8 * (onef - epsf / 4 == onef) + 16 * (onef - epsf / 2 < onef);
  case 2: {
    double h = 0x1p970, hm = 0x1.fffffffffffffp969;
    return fp_id(M + h) * 10 + (M + hm == M);
  }
  case 3: {
    float h = 0x1p103f;
    return fp_id(Mf + h) * 10 + fp_id(Mf * 2.0f);
  }
  case 4: return fp_id(mn / 2);
  case 5: return fp_id(tm / 2) * 10 + fp_id(-tm / 2);
  case 6: return mix(fp_id(tm * 1.5), fp_id(tm * 2.5));
  case 7: return fp_id(mn * 1.5 - mn);
  case 8: return mix(fp_id(mnf / 8388608.0f), fp_id(mnf / 16777216.0f));
  case 9: return fp_id(tmf * 1.5f);
  case 10: {
    float x = 1e30f, y = 1e10f;
    float z = x * y / y;
    return fp_id(z);
  }
  case 11: {
    double a = 1.0 + 0x1p-27, b = 1.0 - 0x1p-27, c = -1.0;
    return fp_id(a * b + c);
  }
  }
  return -2;
}

// long double (x86-64: x87 extended, LDBL_MANT_DIG 64, LDBL_MAX_EXP 16384)
int t_ld(int k) {
  long double one = 1.0L, e = DBL_EPSILON, le = LDBL_EPSILON;
  long long big = 9007199254740993LL;
  switch (k) {
  case 0: return (one + e / 4 > one) + 2 * (one + le > one) + 4 * (one + le / 2 == one);
  case 1: {
    long double x = big;
    return (long long)x == big;
  }
  case 2: {
    long double t = 1e300L;
    t = t * t;
    return (t - t == 0.0L) + 2 * (t > (long double)DBL_MAX);
  }
  }
  return -2;
}

// signed zero (F.9 and IEC 60559): -0 == +0; x + (-x) and (-0) + (+0) are +0
// in round to nearest, (-0) - (+0) and (-0) + (-0) are -0; products,
// quotients and underflow keep the sign; 1/(-0) is -inf; the functions keep
// the sign of a zero argument or result (sqrt(-0) = -0, fmod(-4, 2) = -0,
// ceil(-0.5) = -0, ...), fabs clears it
int t_zero(int k) {
  double z = 0.0, nz = -0.0, x = 3.0, t = 1e-200, tm = DBL_TRUE_MIN, one = 1.0;
  switch (k) {
  case 0:
    return (nz == z) + 2 * sb(nz) + 4 * sb(z * -1.0) + 8 * sb(nz + z) + 16 * sb(nz - z) + 32 * sb(nz + nz) +
           64 * sb(x - x) + 128 * sb(-x * z) + 256 * sb(z / -x) + 512 * sb(-(x - x));
  case 1:
    return sb(-t * t) + 2 * sb(t * -t) + 4 * sb(-tm / 2) + 8 * sb((float)(-t)) + 16 * sb(nz * nz) + 32 * sb(nz / x);
  case 2: return (one / nz < 0.0) + 2 * (one / z > 0.0) + 4 * (one / nz == -(one / z)) + 8 * (one / nz < -DBL_MAX);
  case 3: {
    double m4 = -4.0, two = 2.0, mh = -0.5, m04 = -0.4, m09 = -0.9;
    return sb(sqrt(nz)) + 2 * sb(fmod(nz, one)) + 4 * sb(fmod(m4, two)) + 8 * sb(ceil(mh)) + 16 * sb(round(m04)) +
           32 * sb(trunc(m09)) + 64 * sb(floor(nz)) + 128 * sb(fabs(nz)) + 256 * sb(cbrt(nz)) + 512 * sb(sin(nz)) +
           1024 * sb(tan(nz)) + 2048 * sb(atan(nz));
  }
  case 4: {
    float fz = -0.0f, q = 0.25f, f6 = 6.0f, f3 = 3.0f;
    return sb(fz) + 2 * sb(fz * 2.0f) + 4 * sb(fz + 0.0f) + 8 * sb(sqrtf(fz)) + 16 * sb(ceilf(-q)) +
           32 * sb(roundf(-q)) + 64 * sb(fmodf(-f6, f3)) + 128 * sb(truncf(-q));
  }
  }
  return -2;
}

// conversions: floating to integer truncates toward zero and is defined
// whenever the truncated value fits (6.3.1.4p1: (unsigned)-0.9 is 0,
// (int)2147483647.9 is INT_MAX, 2^63 fits unsigned long long); integer to
// floating rounds to nearest even (6.3.1.4p2, F.4), also for unsigned values
// at and above 2^63; double to float rounds once to nearest even, overflows to
// inf past the midpoint between FLT_MAX and 2^128, underflows to (signed) 0
// (6.3.1.5, F.3; C++ [conv.double]: inf is the adjacent float value)
int t_conv(int k) {
  double a = -2.9, b = 2.9, c = -0.9, imax = 2147483647.9, imin = -2147483648.9, umax = 4294967295.9;
  double ll63m = 9223372036854774784.0, p63 = 9223372036854775808.0, ull64m = 18446744073709549568.0;
  float f32m = 4294967040.0f;
  int i24p1 = 16777217, i24p3 = 16777219, im = -33554435, imx = INT_MAX;
  long long l53p1 = 9007199254740993LL, l53p3 = 9007199254740995LL;
  unsigned long long umx = ULLONG_MAX, u63 = 9223372036854776833ull;  // 2^63 + 1025
  double t24 = 1.0 + 0x1p-24, t24p = 1.0 + 0x1p-24 + 0x1p-52, h128 = 0x1.ffffffp127, h128m = 0x1.fffffefffffffp127;
  double h150 = 0x1p-150, h150p = 0x1p-150 + 0x1p-200, tiny = -1e-50, M = DBL_MAX;
  switch (k) {
  case 0: return (int)a * 1000 + (int)b * 100 + (int)c * 10 + (int)(unsigned)c;
  case 1: return ((int)imax == INT_MAX) + 2 * ((int)imin == INT_MIN);
  case 2: return fold((unsigned)umax);
  case 3: return fold((unsigned long long)(long long)ll63m);
  case 4: return fold((unsigned long long)p63);
  case 5: return fold((unsigned long long)ull64m);
  case 6: return fold((unsigned)f32m);
  case 7:
    return ((int)(float)i24p1 - 16777216) + ((int)(float)i24p3 - 16777216) * 10 +
           ((int)(float)im + 33554432) * 100;
  case 8: return fp_id((float)imx);
  case 9: return mix(fp_id((double)l53p1), fp_id((double)l53p3));
  case 10: return mix(fp_id((double)umx), fp_id((double)u63));
  case 11: return mix(fp_id((float)t24), fp_id((float)t24p));
  case 12: return mix(fp_id((float)h128), fp_id((float)h128m));
  case 13: return mix(mix(fp_id((float)h150), fp_id((float)h150p)), fp_id((float)tiny) * 10 + fp_id((float)M));
  }
  return -2;
}

// the math functions cirlean computes exactly (7.12, F.10): sqrt (correctly
// rounded; -1 gives NaN), fabs, round (halfway away from zero: round(-0.5) is
// -1, round(0.49999999999999994) is 0), floor/ceil/trunc near 2^52 and at the
// least subnormal, fmod (exact; the sign of x; fmod(x, inf) = x; fmod(inf, y)
// and fmod(x, 0) are NaN), fmin/fmax (a NaN argument is missing data; the
// sign of a zero result is glibc's, F.10.9.2 only recommends it)
int t_mx(int k) {
  double two = 2.0, tm = DBL_TRUE_MIN, m1 = -1.0, inf = __builtin_inf(), q = __builtin_nan(""), nz = -0.0, z = 0.0;
  switch (k) {
  case 0: return fp_id(sqrt(two));
  case 1: return fp_id(sqrt(tm));
  case 2: {
    float f = -2.5f;
    return (sqrt(m1) != sqrt(m1)) + 2 * (sqrt(inf) == inf) + 4 * sb(fabs(nz)) + 8 * (fabs(-inf) == inf) +
           16 * (fabs(q) != fabs(q)) + 32 * (fabsf(f) == 2.5f);
  }
  case 3: {
    double h = 0.5, t25 = 2.5, nh = 0.49999999999999994;
    return (int)round(h) + 10 * (int)round(-h) + 100 * (int)round(t25) + 1000 * (int)round(nh) +
           10000 * (int)round(-t25);
  }
  case 4: {
    double p52 = 4503599627370497.0;
    return fp_id(round(p52));
  }
  case 5: {
    float nhf = 0.49999997f, t25 = -2.5f;
    return (int)roundf(nhf) + 10 * (int)roundf(t25) + 100 * (int)floorf(t25) + 1000 * (int)ceilf(t25);
  }
  case 6: {
    double a = 4503599627370495.5;
    return (floor(a) == 4503599627370495.0) + 2 * (ceil(a) == 4503599627370496.0) +
           4 * (floor(-a) == -4503599627370496.0) + 8 * (round(-a) == -4503599627370496.0) +
           16 * (trunc(-a) == -4503599627370495.0);
  }
  case 7: {
    double e300 = 1e300;
    return (floor(tm) == 0) + 2 * (ceil(tm) == 1) + 4 * (floor(-tm) == -1) + 8 * (ceil(-tm) == 0 && sb(ceil(-tm))) +
           16 * (floor(inf) == inf) + 32 * (floor(q) != floor(q)) + 64 * (trunc(-e300) == -e300);
  }
  case 8: {
    double e300 = 1e300, three = 3.0;
    return fp_id(fmod(e300, three));
  }
  case 9: {
    double p1 = 0.1, p01 = 0.01;
    return fp_id(fmod(p1, p01));
  }
  case 10: {
    double M = DBL_MAX;
    return fp_id(fmod(M, tm));
  }
  case 11: {
    double a = 5.5, b = 2.0, c = 5.0, three = 3.0;
    float x = 7.5f, y = 2.0f;
    return (fmod(a, b) == 1.5) + 2 * (fmod(-a, b) == -1.5) + 4 * (fmod(a, -b) == 1.5) + 8 * (fmod(three, inf) == three) +
           16 * (fmod(inf, b) != fmod(inf, b)) + 32 * (fmod(b, z) != fmod(b, z)) + 64 * sb(fmod(-c, c)) +
           128 * (fmodf(x, y) == 1.5f);
  }
  case 12: {
    double one = 1.0;
    float qf = __builtin_nanf(""), f2 = 2.0f, fm1 = -1.0f;
    return (fmin(q, one) == 1) + 2 * (fmax(one, q) == 1) + 4 * (fmin(q, q) != fmin(q, q)) + 8 * (fmin(-inf, z) == -inf) +
           16 * sb(fmax(nz, z)) + 32 * sb(fmin(nz, z)) + 64 * sb(fmax(z, nz)) + 128 * sb(fmin(z, nz)) +
           256 * (fminf(qf, f2) == 2.0f) + 512 * (fmaxf(fm1, -f2) == -1.0f);
  }
  }
  return -2;
}

// the transcendental functions (7.12; F.10 special values): exp, log, log2,
// log10, pow (F.10.4.4: pow(-0, -3) = -inf, pow(x, +-0) = 1 even for NaN x,
// pow(1, y) = 1 even for NaN y, pow(-1, +-inf) = 1, ...), sin, cos, tan with
// a huge argument, atan and atan2 at signed zeros and infinities, cbrt, and
// the float versions
int t_tx(int k) {
  double one = 1.0, nz = -0.0, z = 0.0, inf = __builtin_inf(), q = __builtin_nan(""), tm = DBL_TRUE_MIN;
  double m1 = -1.0, two = 2.0, half = 0.5, m2 = -2.0, m8 = -8.0, third = 1.0 / 3.0;
  switch (k) {
  case 0: return fp_id(exp(one));
  case 1: {
    double a = 710.0, b = -746.0, c = 709.78;
    return (exp(nz) == 1) + 2 * (exp(-inf) == 0 && !sb(exp(-inf))) + 4 * (exp(inf) == inf) + 8 * (exp(a) == inf) +
           16 * (exp(b) == 0) + 32 * (exp(q) != exp(q)) + 64 * (exp(c) < inf);
  }
  case 2:
    return (log(one) == 0 && !sb(log(one))) + 2 * (log(z) == -inf) + 4 * (log(nz) == -inf) +
           8 * (log(m1) != log(m1)) + 16 * (log(inf) == inf);
  case 3: {
    double e8 = 8.0, k3 = 1000.0, s = 1e-300;
    return (log2(e8) == 3) + 2 * (log2(tm) == -1074) + 4 * (log10(k3) == 3) + 8 * (log10(s) == -300) +
           16 * (log2(z) == -inf) + 32 * (log10(m1) != log10(m1));
  }
  case 4: {
    double a = 0.75;
    return mix(fp_id(log2(a)), fp_id(log10(two)));
  }
  case 5: {
    double m3 = -3.0, p3 = 3.0, e1024 = 1024.0;
    return (pow(nz, m3) == -inf) + 2 * (pow(z, m3) == inf) + 4 * (pow(nz, m2) == inf) +
           8 * (pow(nz, p3) == 0 && sb(pow(nz, p3))) + 16 * (pow(m1, inf) == 1) + 32 * (pow(one, q) == 1) +
           64 * (pow(q, z) == 1) + 128 * (pow(m2, half) != pow(m2, half)) + 256 * (pow(half, inf) == 0) +
           512 * (pow(-inf, m3) == 0 && sb(pow(-inf, m3))) + 1024 * (pow(-inf, p3) == -inf) +
           2048 * (pow(two, e1024) == inf) + 4096 * (pow(m8, third) != pow(m8, third));
  }
  case 6: {
    double a = -1074.0, b = -1075.0, ten = 10.0, e22 = 22.0;
    return mix(mix(fp_id(pow(two, a)), fp_id(pow(two, b))), fp_id(pow(ten, e22)));
  }
  case 7: {
    double a = 1e22, h = 1.5707963267948966;
    return mix(mix(fp_id(sin(a)), fp_id(cos(a))), fp_id(tan(h)));
  }
  case 8:
    return sb(sin(nz)) + 2 * (sin(inf) != sin(inf)) + 4 * (cos(nz) == 1) + 8 * sb(tan(nz)) + 16 * (cos(q) != cos(q));
  case 9: {
    int h = fp_id(atan(inf));
    h = mix(h, fp_id(atan(-inf)));
    h = mix(h, fp_id(atan2(z, nz)));
    h = mix(h, fp_id(atan2(nz, nz)));
    h = mix(h, fp_id(atan2(z, z)));
    h = mix(h, fp_id(atan2(nz, z)));
    h = mix(h, fp_id(atan2(z, m1)));
    h = mix(h, fp_id(atan2(nz, m1)));
    h = mix(h, fp_id(atan2(one, z)));
    h = mix(h, fp_id(atan2(inf, inf)));
    h = mix(h, fp_id(atan2(-inf, -inf)));
    h = mix(h, fp_id(atan2(one, -inf)));
    h = mix(h, fp_id(atan2(q, one)));
    return h;
  }
  case 10: {
    double c27 = 27.0;
    return (cbrt(m8) == -2) + 2 * sb(cbrt(nz)) + 4 * (cbrt(-inf) == -inf) + 8 * (cbrt(c27) == 3) +
           16 * (cbrt(q) != cbrt(q)) + 32 * (fp_id(cbrt(tm)) % 2);
  }
  case 11: {
    float a = 1.5f, b = 3.0f, c = 2.0f, d = 0.5f;
    int h = fp_id(expf(a));
    h = mix(h, fp_id(logf(b)));
    h = mix(h, fp_id(powf(c, d)));
    h = mix(h, fp_id(log2f(b)));
    h = mix(h, fp_id(log10f(b)));
    return h;
  }
  case 12: {
    float a = 1.0f, b = 100.0f, c = -0.5f, fz = -0.0f, fm1 = -1.0f, m27 = -27.0f;
    int h = fp_id(sinf(a));
    h = mix(h, fp_id(cosf(b)));
    h = mix(h, fp_id(tanf(c)));
    h = mix(h, fp_id(atanf(b)));
    h = mix(h, fp_id(atan2f(fz, fm1)));
    h = mix(h, fp_id(cbrtf(m27)));
    return h;
  }
  }
  return -2;
}

// classification (7.12.3): subnormals are neither normal nor zero; NaN is not
// finite; -NaN is still NaN
int t_cls(int k) {
  double tm = DBL_TRUE_MIN, nz = -0.0, inf = __builtin_inf(), q = __builtin_nan(""), mn = DBL_MIN, M = DBL_MAX;
  float mnf = FLT_MIN, tmf = FLT_TRUE_MIN, Mf = FLT_MAX;
  if (k == 0)
    return (std::fpclassify(tm) == FP_SUBNORMAL) + 2 * (std::fpclassify(nz) == FP_ZERO) +
           4 * (std::fpclassify(inf) == FP_INFINITE) + 8 * (std::fpclassify(q) == FP_NAN) +
           16 * (std::fpclassify(mn) == FP_NORMAL) + 32 * (std::fpclassify(tmf) == FP_SUBNORMAL);
  return std::isnormal(mn) + 2 * std::isnormal(mn / 2) + 4 * std::isfinite(q) + 8 * std::isinf(-inf) +
         16 * std::isnan(-q) + 64 * std::isfinite(M) + 128 * std::isnormal(mnf) + 256 * std::isnormal(mnf / 2) +
         512 * std::isinf(Mf * 2.0f);
}

// the sign of a NaN: unary minus (IEC 60559 negate) flips it and fabs (abs,
// F.10.4.2) clears it, also for a NaN
int t_nan(int k) {
  double q = __builtin_nan("");
  return std::signbit(q) + 2 * std::signbit(-q) + 4 * std::signbit(fabs(-q)) + 8 * std::signbit(-(-q)) + 16 * k;
}

// undefined behaviour, not expected to match: a floating value whose
// truncation the integer type cannot represent (C11 6.3.1.4p1; F.4 makes it
// an unspecified value with "invalid", C++ [conv.fpint]/1 keeps it undefined):
// 0 2^31 to int, 1 NaN to int, 2 -1.0 to unsigned, 3 2^63 to long long
int ub_fpx(int k) {
  double p31 = 2147483648.0, q = __builtin_nan(""), m1 = -1.0, p63 = 9223372036854775808.0;
  switch (k) {
  case 0: return (int)p31;
  case 1: return (int)q;
  case 2: return (int)((unsigned)m1 % 1000u);
  case 3: return (int)((long long)p63 % 1000);
  }
  return -2;
}
