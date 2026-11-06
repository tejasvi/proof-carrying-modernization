/* The C library's hypot, hypotf, expm1, log1p, erf, erfc, tgamma and lgamma (a C source, run with
   CASES=libm1_cases.txt), which Lean's Float has no operation for: cirlean computes them as glibc
   2.43 computes them on the reference machine, bit for bit (the first four as its x86-64-v3 build's
   code does, with fused multiply-adds; the last four correctly rounded, as CORE-MATH's code is). A
   case returns a hash of the exact bits of its results, or the bits of one result folded to an
   int; a NaN result counts as one value (Lean's Float keeps no NaN sign or payload). The *_rand
   cases draw their inputs from a seeded generator, over the whole range and around each
   function's thresholds. Expected result, labelled per case in the cases file: MATCH, or UB from
   cirrun. */
#include <complex.h>
#include <float.h>
#include <math.h>
#include <stdint.h>

static uint64_t bits(double d) {
  union { double d; uint64_t u; } c;
  c.d = d;
  return c.u;
}
static uint64_t h;
static void mix(double r) {
  h = (h ^ (isnan(r) ? 0x7FF8000000000000ull : bits(r))) * 0x100000001B3ull;
  h ^= h >> 29;
}
static int hash(void) { return (int)(h ^ (h >> 32)); }
/* one result: its bits folded, 7 for a NaN */
static int one(double r) { return isnan(r) ? 7 : (int)(bits(r) ^ (bits(r) >> 32)); }

static uint64_t st;
static uint64_t next(void) {
  uint64_t z = (st += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}
static void seed(int s) {
  st = (uint64_t)s * 0x5851F42D4C957F2Dull + 1;
  h = 0xCBF29CE484222325ull;
}
/* v * 2^e, in steps of at most 2^512 */
static double scale(double v, int e) {
  while (e > 512) { v = v * 0x1p512; e -= 512; }
  while (e < -512) { v = v * 0x1p-512; e += 512; }
  double p = 1.0, b = 2.0;
  int a = e < 0 ? -e : e;
  while (a) {
    if (a & 1) p = p * b;
    b = b * b;
    a >>= 1;
  }
  return e < 0 ? v / p : v * p;
}
/* a random 53-bit mantissa times 2^e, e uniform in [lo, hi], a random sign */
static double rnd(int lo, int hi) {
  uint64_t r = next();
  double m = scale((double)((r >> 11) | (1ull << 52)), (int)(next() % (uint64_t)(hi - lo + 1)) + lo - 52);
  return (r & 1) ? -m : m;
}
static int below(int n) { return (int)(next() % (uint64_t)n); }

/* hypot: special values, the scaling limits 2^511 and 2^-459 and their neighbours, the 2^-54
   ratio; row i: hypot(e[i], e[j]) for every j */
static const double hyp_e[25] = {
  0.0, -0.0, INFINITY, -INFINITY, NAN, 1.0, -1.0, 3.0, 4.0, DBL_MAX, -DBL_MAX, DBL_MIN, 0x1p-1074,
  -0x1p-1074, 0x1p511, 0x1.0000000000001p511, 0x1.fffffffffffffp510, 0x1p-459,
  0x1.0000000000001p-459, 0x1.fffffffffffffp-460, 0x1p-54, 0x1.6a09e667f3bcdp511, 0x1p1023, 1.5,
  -2.75};
int t_hypot_row(int i) {
  seed(0);
  for (int j = 0; j < 25; j++) mix(hypot(hyp_e[i], hyp_e[j]));
  return hash();
}
/* hypot(±inf, NaN) = +inf (C11 F.10.4.3), hypot(NaN, 1) a NaN, exact results */
int t_hypot_special(int k) {
  return (hypot(INFINITY, NAN) == INFINITY) + 2 * (hypot(NAN, -INFINITY) == INFINITY) +
         4 * (isnan(hypot(NAN, 1.0)) != 0) + 8 * (hypot(3.0, -4.0) == 5.0) +
         16 * (hypot(-0.0, -0.0) == 0.0 && !signbit(hypot(-0.0, -0.0))) +
         32 * (hypot(-7.5, 0.0) == 7.5) + 64 * (hypot(DBL_MAX, DBL_MAX) == INFINITY) + k;
}
/* 200 random pairs: anywhere, close magnitudes, around 2^511, around 2^-459 */
int t_hypot_rand(int s) {
  seed(s);
  for (int i = 0; i < 200; i++) {
    double x, y;
    int c = below(4), e;
    if (c == 0) { x = rnd(-1074, 1023); y = rnd(-1074, 1023); }
    else if (c == 1) { e = below(2098) - 1074; x = rnd(e, e); y = rnd(e - below(58), e); }
    else if (c == 2) { e = 508 + below(6); x = rnd(e, e); y = rnd(e - below(58), e); }
    else { e = -462 + below(6); x = rnd(e, e); y = rnd(e, e + below(58)); }
    mix(hypot(x, y));
  }
  return hash();
}

static const float hypf_e[16] = {
  0.0f, -0.0f, INFINITY, -INFINITY, NAN, 1.0f, 3.0f, -4.0f, FLT_MAX, FLT_MIN, 0x1p-149f,
  0x1p64f, 0x1p-64f, 0x1.6a09e6p127f, 1.5f, -0x1.fffffep-127f};
int t_hypotf_row(int i) {
  seed(0);
  for (int j = 0; j < 16; j++) mix(hypotf(hypf_e[i], hypf_e[j]));
  return hash();
}
/* 200 random pairs of floats: anywhere, close magnitudes, near FLT_MAX, subnormal */
int t_hypotf_rand(int s) {
  seed(s);
  for (int i = 0; i < 200; i++) {
    float x, y;
    int c = below(4), e;
    if (c == 0) { x = (float)rnd(-149, 127); y = (float)rnd(-149, 127); }
    else if (c == 1) { e = below(250) - 126; x = (float)rnd(e, e); y = (float)rnd(e - below(30), e); }
    else if (c == 2) { e = 124 + below(4); x = (float)rnd(e, e); y = (float)rnd(e - below(4), e); }
    else { e = -149 + below(30); x = (float)rnd(e, e); y = (float)rnd(e, e); }
    mix(hypotf(x, y));
  }
  return hash();
}

/* expm1: special values and each side of fdlibm's thresholds (high words 0x3c900000,
   0x3fd62e43, 0x3ff0a2b2, 0x4043687a, 0x40862e42 and the overflow limit) */
static const double em_e[36] = {
  0.0, -0.0, INFINITY, -INFINITY, NAN, 1.0, -1.0, 0.25, -0.3, 0x1.fffffffffffffp-55, 0x1p-54,
  -0x1p-54, 0x1.62e42ffffffffp-2, 0x1.62e43p-2, -0x1.62e43p-2, 0x1.0a2b1ffffffffp0, 0x1.0a2b2p0,
  -0x1.0a2b2p0, 0x1.36879ffffffffp5, 0x1.3687ap5, -0x1.36879ffffffffp5, -0x1.3687ap5,
  0x1.62e41ffffffffp9, 0x1.62e42fefa39efp9, 0x1.62e42fefa39f0p9, -0x1.62e42fefa39f0p9, 10.0,
  20.5, 40.0, -2.0, -20.0, 0x1p-1074, DBL_MAX, -DBL_MAX, 700.0, 1e-10};
int t_expm1_edge(int i) { return one(expm1(em_e[i])); }
/* 200 random arguments: anywhere, |x| in [2^-60, 2^10), on [-40, 710], around (j + 1/2) ln 2 */
int t_expm1_rand(int s) {
  seed(s);
  for (int i = 0; i < 200; i++) {
    double x;
    int c = below(4);
    if (c == 0) x = rnd(-1074, 1023);
    else if (c == 1) x = rnd(-60, 9);
    else if (c == 2) x = (double)(below(750000000) - 40000000) * 1e-6;
    else x = ((double)(below(1080) - 56) + 0.5) * 0x1.62e42fefa39efp-1;
    mix(expm1(x));
  }
  return hash();
}

/* log1p: special values, -1 and below, 2^k - 1 (f = 0), each side of fdlibm's thresholds
   (0.41422, -0.2929, 2^-29, 2^-54, 2^53), 1 + x around 2^k √2 */
static const double lp_e[36] = {
  0.0, -0.0, INFINITY, -INFINITY, NAN, -1.0, -0x1.fffffffffffffp-1, -0x1.0000000000001p0, -2.0,
  1.0, 3.0, 7.0, -0.5, -0.75, 0x1.fffffffffffffp-30, 0x1p-29, -0x1p-29, 0x1.fffffffffffffp-55,
  0x1p-54, 0x1.fffffffffffffp52, 0x1p53, DBL_MAX, 0x1.a8279ffffffffp-2, 0x1.a827ap-2,
  -0x1.2bec3ffffffffp-2, -0x1.2bec4p-2, 0x1.6a09dffffffffp0, 0x1.6a09ep0, 0x1.d413cp0, 1e-300,
  0x1p-1074, 1e10, -0.999, 0.1, 2.5, 1e300};
int t_log1p_edge(int i) { return one(log1p(lp_e[i])); }
/* 200 random arguments: anywhere, (-1, -2^-60], (-1, 1), (0, 2^63) */
int t_log1p_rand(int s) {
  seed(s);
  for (int i = 0; i < 200; i++) {
    double x;
    int c = below(4);
    if (c == 0) x = rnd(-1074, 1023);
    else if (c == 1) x = -fabs(rnd(-60, -1));
    else if (c == 2) x = (double)below(2000000000) * 1e-9 - 1.0;
    else x = fabs(rnd(-2, 62));
    mix(log1p(x));
  }
  return hash();
}

/* erf: special values, the limit where it rounds to 1, subnormals */
static const double erf_e[20] = {
  0.0, -0.0, INFINITY, -INFINITY, NAN, 1.0, -1.0, 0.5, 6.0, -6.0, 5.9, 5.921587195794507,
  0x1p-1074, -0x1p-1074, DBL_MIN, 1e-300, 2.5, -3.5, 0x1p-30, 4.0};
int t_erf_edge(int i) { return one(erf(erf_e[i])); }
/* 200 random arguments: anywhere, (-7, 7), around 5.9216, (-1, 1) */
int t_erf_rand(int s) {
  seed(s);
  for (int i = 0; i < 200; i++) {
    double x;
    int c = below(4);
    if (c == 0) x = rnd(-1074, 1023);
    else if (c == 1) x = (double)(below(1400000000) - 700000000) * 1e-8;
    else if (c == 2) x = 5.921587195794507 + (double)(below(2001) - 1000) * 0x1p-50;
    else x = rnd(-60, -1);
    mix(erf(x));
  }
  return hash();
}

/* erfc: special values, 2 below -6, subnormal results near 27, +0 from about 27.3 */
static const double erfc_e[21] = {
  0.0, -0.0, INFINITY, -INFINITY, NAN, 1.0, -1.0, 6.0, -6.0, 26.5, 27.0, 27.2, 27.3, 28.0, 30.0,
  0x1p-1074, 0.5, -0.5, 10.0, 1e-20, -5.9};
int t_erfc_edge(int i) { return one(erfc(erfc_e[i])); }
/* 200 random arguments: anywhere, (-7, 30), (26, 27.5), (0, 6) */
int t_erfc_rand(int s) {
  seed(s);
  for (int i = 0; i < 200; i++) {
    double x;
    int c = below(4);
    if (c == 0) x = rnd(-1074, 1023);
    else if (c == 1) x = (double)below(37000000) * 1e-6 - 7.0;
    else if (c == 2) x = 26.0 + (double)below(1500000) * 1e-6;
    else x = (double)below(600000000) * 1e-8;
    mix(erfc(x));
  }
  return hash();
}

/* tgamma: special values, poles, integers (exact factorials, rounded), half-integers, overflow
   past 171.62, underflow below -184 */
static const double tg_e[28] = {
  0.0, -0.0, INFINITY, -INFINITY, NAN, 1.0, 2.0, 3.0, 0.5, -0.5, 1.5, -1.5, 171.0, 171.5, 171.7,
  172.0, -1.0, -2.0, 0x1p-1074, -0x1p-1074, 1e-308, 10.1, -170.5, -184.5, -200.5, 30.0, 25.0,
  100.0};
int t_tgamma_edge(int i) { return one(tgamma(tg_e[i])); }
/* 200 random arguments: (-200, 180), near the integers, small, (170, 172) */
int t_tgamma_rand(int s) {
  seed(s);
  for (int i = 0; i < 200; i++) {
    double x;
    int c = below(4);
    if (c == 0) x = (double)below(380000000) * 1e-6 - 200.0;
    else if (c == 1) x = (double)(below(380) - 200) + rnd(-50, -2);
    else if (c == 2) x = rnd(-1074, 0);
    else x = 170.0 + (double)below(2000000) * 1e-6;
    mix(tgamma(x));
  }
  return hash();
}

/* lgamma: special values, poles, its zeros 1 and 2 and the doubles next to them, near its negative
   zeros, huge arguments */
static const double lg_e[25] = {
  0.0, -0.0, INFINITY, -INFINITY, NAN, 1.0, 2.0, 3.0, 0.5, -0.5, -1.0, -2.5, 0x1.0000000000001p0,
  0x1.fffffffffffffp-1, 0x1.0000000000001p1, 0x1.fffffffffffffp0, -2.4570247382208006,
  -2.7476826467274127, 1e300, DBL_MAX, 0x1p-1074, 100.5, -100.5, 1e10, 0x1p1016};
int t_lgamma_edge(int i) { return one(lgamma(lg_e[i])); }
/* 200 random arguments: (-100, 200), near 1 and 2, near -2.457, anywhere positive */
int t_lgamma_rand(int s) {
  seed(s);
  for (int i = 0; i < 200; i++) {
    double x;
    int c = below(4);
    if (c == 0) x = (double)below(300000000) * 1e-6 - 100.0;
    else if (c == 1) x = (below(2) ? 1.0 : 2.0) + (double)(below(4001) - 2000) * 0x1p-52;
    else if (c == 2) x = -2.4570247382208006 + (double)(below(4001) - 2000) * 0x1p-51;
    else x = fabs(rnd(-1074, 1023));
    mix(lgamma(x));
  }
  return hash();
}

/* control: expm1f, log1pf, erff and cabs have no model (outside this batch) */
int t_expm1f(int k) { return one(expm1f(0.5f)) + k; }
int t_erff(int k) { return one(erff(0.5f)) + k; }
int t_log1pf(int k) { return one(log1pf(0.5f)) + k; }
int t_cabs(int k) {
  double complex z = 3.0 + 4.0 * I;
  return one(cabs(z)) + k;
}
