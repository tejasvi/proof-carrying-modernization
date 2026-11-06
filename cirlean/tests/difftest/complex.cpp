// Complex numbers (GNU C++ _Complex): the parts and their addresses (__real__, __imag__),
// + - unary - and ~ (the conjugate), == and !=, conversions, constants, complex values in memory,
// and * and / through the runtime library's __muldc3 / __divdc3 / __mulsc3 / __divsc3 (libgcc's
// algorithms: C11 Annex G's recovery of infinities and zeros, Smith's division with scaling), at
// the inputs where the algorithms branch. A result is compared through a hash of its parts
// printed exactly (%.17g; a NaN prints as "nan" whatever its sign).
#include <cfloat>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <cstring>

typedef double _Complex dc;
typedef float _Complex fc;
typedef int _Complex ic;

static int hash_str(const char *s) {
  unsigned h = 5381;
  for (; *s; ++s) h = h * 33 + (unsigned char)*s;
  return (int)(h & 0x7fffffff);
}
static int part(char *p, double x) {
  if (x != x) return sprintf(p, "nan|");
  return sprintf(p, "%.17g|", x);
}
static int hc(dc z) {
  char buf[96];
  int n = part(buf, __real__ z);
  part(buf + n, __imag__ z);
  return hash_str(buf);
}
// a float's parts are exact as doubles
static int hf(fc z) { return hc(z); }
static dc mk(double re, double im) {
  dc z;
  __real__ z = re;
  __imag__ z = im;
  return z;
}
static fc mkf(float re, float im) {
  fc z;
  __real__ z = re;
  __imag__ z = im;
  return z;
}
static ic mki(int re, int im) {
  ic z;
  __real__ z = re;
  __imag__ z = im;
  return z;
}

// the parts, read and written, and their addresses: two consecutive doubles
int t_parts(int k) {
  dc z = mk(1.5, -2.25);
  double *p = &__real__ z, *q = &__imag__ z;
  switch (k) {
  case 0: return (int)(__real__ z * 4);
  case 1: return (int)(__imag__ z * 4);
  case 2: *p = 7; *q = 8; return hc(z);
  case 3: return p + 1 == q;
  case 4: p[1] = 3; return hc(z);
  }
  return -1;
}
// the parts of real values: the value itself, and 0
int t_real_parts(int k) {
  double d = -2.5;
  int n = 7;
  switch (k) {
  case 0: return hc(mk(__real__ d, __imag__ d));
  case 1: return __real__ n * 10 + __imag__ n;
  }
  return -1;
}

static const double AV[][4] = {
  {1, 2, 3, 4}, {0.1, 0.2, 0.3, 0.7}, {-0.0, 0.0, 0.0, -0.0}, {1e308, -1e308, 1e308, -1e308},
  {INFINITY, 1, -INFINITY, 2}, {NAN, 1, 2, 3},
};
// + and -, in place, and with a real operand (whose imaginary part is not added)
int t_add(int i, int k) {
  dc a = mk(AV[i][0], AV[i][1]), b = mk(AV[i][2], AV[i][3]);
  switch (k) {
  case 0: return hc(a + b);
  case 1: return hc(a - b);
  case 2: a += b; return hc(a);
  case 3: a -= b; return hc(a);
  case 4: return hc(a + AV[i][2]);
  case 5: return hc(AV[i][2] - a);
  }
  return -1;
}
// unary -, ~ (the conjugate) and +
int t_neg(int i, int k) {
  dc a = mk(AV[i][0], AV[i][1]);
  switch (k) {
  case 0: return hc(-a);
  case 1: return hc(~a);
  case 2: return hc(+a);
  }
  return -1;
}
// _Complex int: + - unary - ~ ==, and * / (computed inline)
int t_int(int k) {
  ic a = mki(7, -3), b = mki(-2, 5), c;
  switch (k) {
  case 0: c = a + b; break;
  case 1: c = a - b; break;
  case 2: c = -a; break;
  case 3: c = ~a; break;
  case 4: return a == b;
  case 5: return a != b;
  case 6: return a == mki(7, -3);
  case 7: c = a * b; break;
  case 8: c = a / b; break;
  default: return -1;
  }
  return __real__ c * 1000 + __imag__ c;
}

static const double EV[][4] = {
  {1, 2, 1, 2}, {1, 2, 1, 3}, {1, 2, 0, 2}, {0.0, -0.0, -0.0, 0.0}, {NAN, 0, NAN, 0},
  {1, NAN, 1, NAN}, {INFINITY, 1, INFINITY, 1},
};
// == and !=: both parts equal (-0 == +0; a NaN part is unequal)
int t_eq(int i) {
  dc a = mk(EV[i][0], EV[i][1]), b = mk(EV[i][2], EV[i][3]);
  return (a == b) * 10 + (a != b);
}

// conversions between complex types, to and from real types, to bool
int t_conv(int k) {
  dc a = mk(1.0000000000000002, -0.1);
  fc f = mkf(2.5f, -0.75f);
  ic n = mki(-7, 9);
  switch (k) {
  case 0: { fc g = a; return hf(g); }
  case 1: { dc z = f; return hc(z); }
  case 2: { fc g = n; return hf(g); }
  case 3: { dc z = 2.5; return hc(z); }
  case 4: { dc z = n; return hc(z); }
  case 5: { ic m = a * 10.0; return __real__ m * 100 + __imag__ m; }
  case 6: return a ? 1 : 0;
  case 7: return mk(0.0, -0.0) ? 1 : 0;
  case 8: return mk(0.0, NAN) ? 1 : 0;
  case 9: return !mk(0.0, 1e-300);
  case 10: return (int)__real__ (a * 3.0);
  }
  return -1;
}

dc g_one = 3.0;
fc g_f;
dc g_arr[3] = {1.0, 2.5, -4.0};
struct cs {
  char c;
  dc z;
  fc f;
} g_s = {1, 5.0, 2.0f};
// constants: globals, an array and a struct member of complex type; size, alignment, layout
int t_const(int k) {
  switch (k) {
  case 0: return hc(g_one);
  case 1: return hf(g_f);
  case 2: return hc(g_arr[1]) ^ hc(g_arr[2]);
  case 3: return hc(g_s.z) ^ hf(g_s.f) ^ g_s.c;
  case 4: return (int)sizeof(dc) * 1000 + (int)alignof(dc) * 100 + (int)sizeof(fc) * 10 + (int)alignof(fc);
  case 5: return (int)offsetof(cs, z) * 100 + (int)offsetof(cs, f);
  case 6: { dc z = 2.5; z += g_one; return hc(z); }
  }
  return -1;
}

// complex values in memory: an array walked by a pointer, a member through a pointer, memcpy,
// a select between two values
int t_mem(int k) {
  dc a[4];
  for (int i = 0; i < 4; ++i) a[i] = mk(i, -i);
  switch (k) {
  case 0: { dc s = 0; for (dc *p = a; p != a + 4; ++p) s += *p; return hc(s); }
  case 1: { cs s = {2, mk(1, 2), mkf(3, 4)}; cs *p = &s; __imag__ p->z = 9; return hc(p->z) ^ hf(p->f); }
  case 2: { double d[2]; memcpy(d, &a[3], sizeof d); return (int)(d[0] * 10 + d[1]); }
  case 3: { dc z; memcpy(&z, &a[2], sizeof z); return hc(z); }
  case 4: { dc z = k > 3 ? a[1] : a[2]; return hc(z); }
  }
  return -1;
}

static const double MV[][4] = {
  {1, 2, 3, 4},
  {0.1, 0.2, 0.3, 0.7},
  {-1.25, 3.5, 2.75, -0.5},
  {1e300, 1e300, 1e10, 1e10},
  {INFINITY, INFINITY, 0, 1},
  {INFINITY, NAN, 1, 0},
  {0, 1, INFINITY, INFINITY},
  {INFINITY, 0, 0, 0},
  {NAN, 1e300, 1e300, 1e300},
  {NAN, NAN, 1, 2},
  {-0.0, -0.0, -0.0, 0.0},
  {DBL_MAX, DBL_MAX, 2, -2},
  {1e-200, 1e-200, 1e-200, 1e-200},
  {3, -4, -NAN, 1},
};
// a * b (__muldc3 when the product's parts are both NaN), and *=
int t_mul(int i) { return hc(mk(MV[i][0], MV[i][1]) * mk(MV[i][2], MV[i][3])); }
int t_mul_in(int i) {
  dc z = mk(MV[i][0], MV[i][1]);
  z *= mk(MV[i][2], MV[i][3]);
  return hc(z);
}

static const double DV[][4] = {
  {1, 2, 3, 4},
  {0.1, 0.2, 0.3, 0.7},
  {5.5, -2.25, 1.1, 0.3},
  {1, 1, 0, 0},
  {1, -1, -0.0, 0},
  {0, 0, 0, 0},
  {INFINITY, NAN, 1, 2},
  {1, 2, INFINITY, INFINITY},
  {-0.0, 1, INFINITY, -NAN},
  {-0.0, 1, INFINITY, NAN},
  {1e308, 1e308, 1e308, 1e308},
  {1, 1, 1e-300, 2e-300},
  {1e-310, 1, 3, 4},
  {1, 1, 1e-310, 1},
  {1, 1, 1, 1e-310},
  {DBL_MAX, DBL_MAX, DBL_MAX / 4, DBL_MAX},
  {3, 7, 2, 5},
  {123.456, -7.89, 0.0123, 45.6},
  {1, 0, 3, 1e-20},
  {NAN, 1, 2, 3},
  {INFINITY, INFINITY, INFINITY, INFINITY},
  {2.2250738585072014e-308, 1e-300, 1e-305, 3e-306},
  {0.7, -1.3, 2.9, 0.1},
  {1e-5, 3e5, -7.7, 2.2},
  {-123.25, 0.001, 9.5, -88.125},
  {0.3, 0.6, 0.9, 1.2},
};
// a / b (__divdc3), and /=
int t_div(int i) { return hc(mk(DV[i][0], DV[i][1]) / mk(DV[i][2], DV[i][3])); }
int t_div_in(int i) {
  dc z = mk(DV[i][0], DV[i][1]);
  z /= mk(DV[i][2], DV[i][3]);
  return hc(z);
}

static const float FMV[][4] = {
  {1, 2, 3, 4},
  {0.1f, 0.2f, 0.3f, 0.7f},
  {1e30f, 1e30f, 1e10f, 1e10f},
  {INFINITY, INFINITY, 0, 1},
  {NAN, 1e30f, 1e30f, 1e30f},
  {FLT_MAX, FLT_MAX, 2, -2},
  {1.5f, -2.5f, -0.0f, 0.0f},
  {3.14159f, -2.71828f, 1.41421f, 1.73205f},
};
// float: a * b (__mulsc3)
int t_mulf(int i) { return hf(mkf(FMV[i][0], FMV[i][1]) * mkf(FMV[i][2], FMV[i][3])); }

static const float FDV[][4] = {
  {1, 2, 3, 4},
  {0.1f, 0.2f, 0.3f, 0.7f},
  {5.5f, -2.25f, 1.1f, 0.3f},
  {1, 1, 0, 0},
  {INFINITY, NAN, 1, 2},
  {1, 2, INFINITY, INFINITY},
  {-0.0f, 1, INFINITY, -NAN},
  {1e20f, 1e20f, 1e20f, 1e20f},
  {1, 1, 1e-40f, 2e-40f},
  {3, 7, 2, 5},
  {FLT_MAX, FLT_MAX, 1, 1},
  {3.14159f, -2.71828f, 1.41421f, 1.73205f},
};
// float: a / b (__divsc3, computed in double)
int t_divf(int i) { return hf(mkf(FDV[i][0], FDV[i][1]) / mkf(FDV[i][2], FDV[i][3])); }

// an indeterminate imaginary part, read (undefined)
int u_indeterminate() {
  dc z;
  __real__ z = 1;
  return (int)(__imag__ z + 1);
}
// long double complex division calls __divxc3, which has no model (x87 extended precision)
int g_div_ld() {
  long double _Complex a = 1, b = 4;
  return (int)(__real__ (a / b) * 8);
}
