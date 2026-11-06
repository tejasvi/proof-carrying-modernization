// More <math.h> functions (run with CASES=math2_cases.txt): asin, acos, sinh,
// cosh, tanh, asinh, acosh, atanh and exp2, and their float versions, through
// Lean's Float, which calls the same C library functions. A case returns a
// mix of the result's bits (a union reads a double as an integer of its size),
// so it compares the exact value. Expected result (labelled per case in the
// cases file): MATCH everywhere.
#include <cmath>

static int bits(double d) {
  union { double d; unsigned long long u; } c;
  c.d = d;
  return (int)(c.u ^ (c.u >> 32));
}

static int fbits(float f) {
  union { float f; unsigned u; } c;
  c.f = f;
  return (int)c.u;
}

// x = n / 8
int t_asin(int n) { return bits(asin(n / 8.0)); }
int t_acos(int n) { return bits(acos(n / 8.0)); }
int t_sinh(int n) { return bits(sinh(n / 8.0)); }
int t_cosh(int n) { return bits(cosh(n / 8.0)); }
int t_tanh(int n) { return bits(tanh(n / 8.0)); }
int t_asinh(int n) { return bits(asinh(n / 8.0)); }
int t_acosh(int n) { return bits(acosh(n / 8.0)); }
int t_atanh(int n) { return bits(atanh(n / 8.0)); }
int t_exp2(int n) { return bits(exp2(n / 8.0)); }

int t_asinf(int n) { return fbits(asinf(n / 8.0f)); }
int t_tanhf(int n) { return fbits(tanhf(n / 8.0f)); }
int t_exp2f(int n) { return fbits(exp2f(n / 8.0f)); }

// out of the domain: a NaN (its bits are not compared: Float keeps no NaN sign or payload)
int t_asin_nan(int n) { return std::isnan(asin(n / 8.0)) ? 1 : 0; }
