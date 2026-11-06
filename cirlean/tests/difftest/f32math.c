/* The float versions of the C library's transcendental functions (a C source, run with
   CASES=f32math_cases.txt): sinf, cosf, ..., powf and atan2f are glibc's float functions (Lean's
   Float32 calls them), not the double function rounded to float, which differs from them by one
   unit in the last place on millions of inputs (an exhaustive scan: sinf 29.4M, cosf 28.2M, logf
   417k, log2f 314k, expf 171k, exp2f 168k, and a few for acosf, sinhf, asinhf, acoshf, log10f,
   atanf). A case returns the bits of one result at an input where the two differ, or a hash of 300
   results at random inputs (any finite or infinite float, half of them between 2^-17 and 2^13; a
   NaN result counts as one value). Expected result, labelled per case in the cases file: MATCH. */
#include <math.h>
#include <stdint.h>
#include <string.h>

static float fl(int b) {
  float x;
  memcpy(&x, &b, 4);
  return x;
}
static int bi(float x) {
  int b;
  memcpy(&b, &x, 4);
  return b;
}

int t_sinf(int b) { return bi(sinf(fl(b))); }
int t_cosf(int b) { return bi(cosf(fl(b))); }
int t_tanf(int b) { return bi(tanf(fl(b))); }
int t_asinf(int b) { return bi(asinf(fl(b))); }
int t_acosf(int b) { return bi(acosf(fl(b))); }
int t_atanf(int b) { return bi(atanf(fl(b))); }
int t_sinhf(int b) { return bi(sinhf(fl(b))); }
int t_coshf(int b) { return bi(coshf(fl(b))); }
int t_tanhf(int b) { return bi(tanhf(fl(b))); }
int t_asinhf(int b) { return bi(asinhf(fl(b))); }
int t_acoshf(int b) { return bi(acoshf(fl(b))); }
int t_atanhf(int b) { return bi(atanhf(fl(b))); }
int t_expf(int b) { return bi(expf(fl(b))); }
int t_exp2f(int b) { return bi(exp2f(fl(b))); }
int t_logf(int b) { return bi(logf(fl(b))); }
int t_log2f(int b) { return bi(log2f(fl(b))); }
int t_log10f(int b) { return bi(log10f(fl(b))); }
int t_cbrtf(int b) { return bi(cbrtf(fl(b))); }
int t_powf(int x, int y) { return bi(powf(fl(x), fl(y))); }
int t_atan2f(int y, int x) { return bi(atan2f(fl(y), fl(x))); }

static uint64_t st, h;
static uint64_t next(void) {
  uint64_t z = (st += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}
static void mix(float r) {
  h = (h ^ (isnan(r) ? 0x7FC00000u : (uint32_t)bi(r))) * 0x100000001B3ull;
  h ^= h >> 29;
}
/* a random float that is not a NaN: an infinity for the NaN exponent; every other input between
   2^-17 and 2^13 */
static float rnd(int i) {
  uint32_t b = (uint32_t)next();
  if (i % 2) b = (b & 0x807FFFFFu) | ((uint32_t)(110 + next() % 30) << 23);
  if ((b & 0x7F800000u) == 0x7F800000u) b &= 0xFF800000u;
  return fl((int)b);
}
/* 300 results of function f (0 sinf ... 17 cbrtf, 18 powf, 19 atan2f) at random inputs */
int t_rand(int f, int s) {
  st = (uint64_t)s * 0x5851F42D4C957F2Dull + 1;
  h = 0xCBF29CE484222325ull;
  for (int i = 0; i < 300; i++) {
    float x = rnd(i), r;
    switch (f) {
    case 0: r = sinf(x); break;
    case 1: r = cosf(x); break;
    case 2: r = tanf(x); break;
    case 3: r = asinf(x); break;
    case 4: r = acosf(x); break;
    case 5: r = atanf(x); break;
    case 6: r = sinhf(x); break;
    case 7: r = coshf(x); break;
    case 8: r = tanhf(x); break;
    case 9: r = asinhf(x); break;
    case 10: r = acoshf(x); break;
    case 11: r = atanhf(x); break;
    case 12: r = expf(x); break;
    case 13: r = exp2f(x); break;
    case 14: r = logf(x); break;
    case 15: r = log2f(x); break;
    case 16: r = log10f(x); break;
    case 17: r = cbrtf(x); break;
    case 18: r = powf(x, rnd(i + 1)); break;
    default: r = atan2f(x, rnd(i + 1)); break;
    }
    mix(r);
  }
  return (int)(h ^ (h >> 32));
}
