// Vectors (GNU vector_size): construction, constants and splats, element reads and writes, the element-wise
// operations (+ - * / % & | ^ ~ unary - << >>, comparisons giving 0 / -1, ?: of vectors), shuffles
// (__builtin_shufflevector), conversions (__builtin_convertvector) and bitcasts between vector types, float
// and double vectors, and vectors in memory (globals, arrays, structs, through pointers, memcpy, unions).
// Results are compared through a hash of their elements (floats printed exactly, %.17g; a NaN as "nan").
#include <cstddef>
#include <cstdio>
#include <cstring>

typedef int v4si __attribute__((vector_size(16)));
typedef unsigned v4su __attribute__((vector_size(16)));
typedef short v8hi __attribute__((vector_size(16)));
typedef unsigned char v16qu __attribute__((vector_size(16)));
typedef long long v2di __attribute__((vector_size(16)));
typedef float v4sf __attribute__((vector_size(16)));
typedef double v2df __attribute__((vector_size(16)));
typedef double v4df __attribute__((vector_size(32)));
typedef int v2si __attribute__((vector_size(8)));
typedef int v8si __attribute__((vector_size(32)));
typedef float v2sf __attribute__((vector_size(8)));
typedef signed char v8qi __attribute__((vector_size(8)));
typedef unsigned char v4qu __attribute__((vector_size(4)));

static int mix(unsigned h, long long x) { return (int)((h * 1000003u ^ (unsigned)x ^ (unsigned)(x >> 32)) & 0x7fffffff); }
static int h4(v4si v) { int h = 17; for (int i = 0; i < 4; ++i) h = mix(h, v[i]); return h; }
static int h4u(v4su v) { int h = 17; for (int i = 0; i < 4; ++i) h = mix(h, v[i]); return h; }
static int h8(v8hi v) { int h = 17; for (int i = 0; i < 8; ++i) h = mix(h, v[i]); return h; }
static int h16(v16qu v) { int h = 17; for (int i = 0; i < 16; ++i) h = mix(h, v[i]); return h; }
static int h2l(v2di v) { return mix(mix(17, v[0]), v[1]); }
static int hash_str(const char *s) {
  unsigned h = 5381;
  for (; *s; ++s) h = h * 33 + (unsigned char)*s;
  return (int)(h & 0x7fffffff);
}
static int fpart(char *p, double x) {
  if (x != x) return sprintf(p, "nan|");
  return sprintf(p, "%.17g|", x);
}
static int hf(v4sf v) {
  char buf[128];
  int n = 0;
  for (int i = 0; i < 4; ++i) n += fpart(buf + n, v[i]);
  return hash_str(buf);
}
static int hd(v2df v) {
  char buf[64];
  int n = fpart(buf, v[0]);
  fpart(buf + n, v[1]);
  return hash_str(buf);
}

// element-wise integer operations
int t_int(int k) {
  v4si a = {7, -3, 100, -45}, b = {2, 5, -7, 3}, c;
  switch (k) {
  case 0: c = a + b; break;
  case 1: c = a - b; break;
  case 2: c = a * b; break;
  case 3: c = a / b; break;
  case 4: c = a % b; break;
  case 5: c = a & b; break;
  case 6: c = a | b; break;
  case 7: c = a ^ b; break;
  case 8: c = ~a; break;
  case 9: c = -a; break;
  case 10: c = (a & 0xff) << (v4si){1, 2, 3, 4}; break;
  case 11: c = a >> 1; break;
  case 12: c = a + 1000; break;
  case 13: c = 3 * a - b; break;
  case 14: c = a < b; break;
  case 15: c = a == (v4si){7, 0, 100, 0}; break;
  case 16: c = a >= b; break;
  case 17: c = a != b; break;
  case 18: c = a ? b : (v4si){0, 0, 0, 0}; break;
  case 19: c = (a > 0) ? a : -a; break;
  case 20: { c = a; c += b; c *= 2; c -= 1; break; }
  default: return -1;
  }
  return h4(c);
}
// unsigned elements: wrapping, logical shifts, unsigned comparison and division
int t_uint(int k) {
  v4su a = {7u, 0xFFFFFFF0u, 100u, 0x80000000u}, b = {2u, 5u, 0xFFFFFFFFu, 3u}, c;
  switch (k) {
  case 0: c = a + b; break;
  case 1: c = a - b; break;
  case 2: c = a * b; break;
  case 3: c = a / b; break;
  case 4: c = a % b; break;
  case 5: c = a >> 3; break;
  case 6: c = a << (v4su){1, 2, 31, 0}; break;
  case 7: return h4(a < b);
  default: return -1;
  }
  return h4u(c);
}
// narrow and wide elements
int t_widths(int k) {
  v8hi s = {1, -2, 300, -400, 32767, -32768, 7, 0};
  v16qu q = {0, 1, 2, 3, 250, 251, 252, 253, 254, 255, 10, 20, 30, 40, 50, 60};
  v2di l = {1LL << 40, -5};
  switch (k) {
  case 0: return h8(s + s);
  case 1: return h8(s * (v8hi){2, 2, 2, 2, 2, 2, 2, 2});
  case 2: return h16(q + q);
  case 3: return h16(q / 2);
  case 4: return h2l(l * 3 + l);
  case 5: return h2l(l < (v2di){0, 0});
  }
  return -1;
}
// element reads and writes, with constant and variable indices
int t_elem(int k, int i) {
  v4si a = {10, 20, 30, 40};
  switch (k) {
  case 0: return a[i];
  case 1: a[i] = -1; return h4(a);
  case 2: { v4si b = a; b[i] += a[3 - i]; return h4(b); }
  case 3: { int s = 0; for (int j = 0; j < 4; ++j) s += a[j] * j; return s; }
  }
  return -1;
}

v4si g_v = {1, 2, 3, 4};
v4sf g_f = {0.5f, -1.25f, 3.0f, 1e-3f};
v4si g_z;
v2df g_d = {1.0 / 3, -2.5};
// constants: globals, a zero vector, splats, compound literals
int t_const(int k, int x) {
  switch (k) {
  case 0: return h4(g_v);
  case 1: return hf(g_f);
  case 2: return h4(g_z);
  case 3: return hd(g_d);
  case 4: return h4((v4si){x, x, x, x});
  case 5: return h4(g_v + x);
  case 6: return h4((v4si){x, 2 * x, 3 * x, 4 * x} - g_v);
  case 7: return (int)sizeof(v4si) * 100 + (int)alignof(v4si) * 10 + (int)sizeof(v2si);
  case 8: return (int)sizeof(v8si) * 100 + (int)alignof(v8si);
  }
  return -1;
}
// __builtin_shufflevector: one or two inputs, repeated and reordered elements, other lengths
int t_shuffle(int k) {
  v4si a = {1, 2, 3, 4}, b = {50, 60, 70, 80};
  switch (k) {
  case 0: return h4(__builtin_shufflevector(a, b, 0, 4, 1, 5));
  case 1: return h4(__builtin_shufflevector(a, a, 3, 2, 1, 0));
  case 2: return h4(__builtin_shufflevector(a, b, 7, 7, 0, 0));
  case 3: { v2si c = __builtin_shufflevector(a, b, 2, 6); return c[0] * 1000 + c[1]; }
  case 4: { v8si c = __builtin_shufflevector(a, b, 0, 1, 2, 3, 4, 5, 6, 7); return c[2] * 100 + c[5]; }
  case 5: { v4si c = __builtin_shufflevector(a, b, 1, -1, 4, -1); return c[0] * 100 + c[2]; }
  }
  return -1;
}
// __builtin_convertvector: element conversions (rounding, truncation toward zero)
int t_convert(int k) {
  v4si a = {1, -7, 1 << 25, 2147483647};
  v4sf f = {1.75f, -2.5f, 1e9f, -0.0f};
  v8hi s = {1, -2, 3, -4, 5, -6, 7, -8};
  switch (k) {
  case 0: return hf(__builtin_convertvector(a, v4sf));
  case 1: return h4(__builtin_convertvector(f, v4si));
  case 2: { v4df d = __builtin_convertvector(a, v4df); return hd((v2df){d[2], d[3]}); }
  case 3: { v8si w = __builtin_convertvector(s, v8si); return w[3] * 10 + w[6]; }
  case 4: return h4u(__builtin_convertvector(a, v4su));
  }
  return -1;
}
// bitcasts between vector types: the elements' bytes, little-endian
int t_bitcast(int k) {
  v4si a = {0x01020304, -1, 256, -2147483647 - 1};
  v4sf f = {1.0f, -2.0f, 0.5f, 3.0e-39f};
  v2di l = {0x3FF0000000000000LL, 0x4000000000000000LL};
  switch (k) {
  case 0: return h4u((v4su)a);
  case 1: return h16((v16qu)a);
  case 2: return h2l((v2di)a);
  case 3: return h8((v8hi)a);
  case 4: return h4((v4si)f);
  case 5: return hf((v4sf)(v4si){0x3F800000, 0x40490FDB, 0x00000001, (int)0x80000000});
  case 6: return hd((v2df)l);
  case 7: return h4((v4si)(v16qu){1, 0, 0, 0, 2, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 128});
  }
  return -1;
}
// float and double vectors: arithmetic, negation, comparisons (a NaN element compares unordered)
int t_float(int k) {
  v4sf a = {1.5f, -0.25f, 1e30f, 0.1f}, b = {2.0f, 4.0f, 1e10f, 0.3f};
  v2df x = {0.1, 1e308}, y = {0.2, 10.0};
  switch (k) {
  case 0: return hf(a + b);
  case 1: return hf(a - b);
  case 2: return hf(a * b);
  case 3: return hf(a / b);
  case 4: return hf(-a);
  case 5: return hf(a * b + a);
  case 6: return hd(x + y);
  case 7: return hd(x * y);
  case 8: return hd(x / y - x);
  case 9: return h4(a < b);
  case 10: { v4sf n = a; n[2] = n[2] * 1e30f * 1e30f * 0.0f; return h4(n == n); }
  case 11: return h2l(x >= y);
  }
  return -1;
}
struct vs {
  char c;
  v4si v;
  int tail;
};
// vectors in memory: an array of vectors, a struct member, a pointer, memcpy, a union with an array
int t_mem(int k) {
  v4si arr[3] = {{1, 2, 3, 4}, {5, 6, 7, 8}, {9, 10, 11, 12}};
  switch (k) {
  case 0: { v4si s = {0, 0, 0, 0}; for (v4si *p = arr; p != arr + 3; ++p) s += *p; return h4(s); }
  case 1: { vs s = {1, {2, 3, 4, 5}, 6}; vs *p = &s; p->v[2] = 40; return h4(p->v) + p->tail + p->c; }
  case 2: { int out[4]; memcpy(out, &arr[1], sizeof out); return out[0] * 1000 + out[3]; }
  case 3: { v4si v; int in[4] = {-1, -2, -3, -4}; memcpy(&v, in, sizeof v); return h4(v); }
  case 4: { union { v4si v; int a[4]; } u; u.v = arr[2]; return u.a[1] * 100 + u.a[3]; }
  case 5: return (int)sizeof(vs) * 100 + (int)offsetof(vs, v) * 10 + (int)alignof(vs);
  }
  return -1;
}
// an element index outside the vector (undefined)
int u_index(int i) {
  v4si a = {1, 2, 3, 4};
  return a[i];
}
// integer division by a zero element (undefined)
int u_div0() {
  v4si a = {1, 2, 3, 4}, b = {1, 0, 1, 1};
  return h4(a / b);
}
// the elements of a vector through a pointer to int: (int *)&v designates element 0, and its strides count
// the vector's elements
int t_int_ptr(int k, int i) {
  v4si a = {10, 20, 30, 40};
  int *p = (int *)&a;
  switch (k) {
  case 0: return p[i];
  case 1: p[i] = -5; return h4(a);
  case 2: return (int)(p + 4 - p);
  }
  return -1;
}
// a read one past the vector's last element through a pointer to int (undefined)
int u_int_ptr_past() {
  v4si a = {10, 20, 30, 40};
  int *p = (int *)&a;
  return p[4];
}
// bitcasts between a vector and a scalar of its size, both ways: the value's bytes, little-endian
// (the operands are variables, so that the casts happen at run time, not in Clang's constant folding)
int t_scalar_cast(int k) {
  v2si a = {0x01020304, -2};
  v4si b = {1, -1, 0x7fffffff, 256};
  v2sf g = {1.5f, 1.0f};
  v8qi q = {1, 2, 3, 4, 5, 6, 7, -8};
  v4qu r = {0x78, 0x56, 0x34, 0x12};
  volatile long long l = 0x0000000500000007LL, fl = 0x400000003f800000LL;
  volatile __int128 w = ((__int128)3 << 64) | 9;
  volatile unsigned u = 0x12345678u;
  switch (k) {
  case 0: return mix(17, (long long)a);
  case 1: { v2si c = (v2si)l; return c[0] * 100 + c[1]; }
  case 2: { __int128 x = (__int128)b; return mix(mix(17, (long long)x), (long long)(x >> 64)); }
  case 3: return h4((v4si)w);
  case 4: return mix(17, (long long)g);
  case 5: { v2sf f = (v2sf)fl; return (int)(f[0] * 10) * 100 + (int)(f[1] * 10); }
  case 6: return mix(17, (long long)q);
  case 7: return (int)((unsigned)r >> 1);
  case 8: { v4qu c = (v4qu)u; return c[0] * 1000 + c[3]; }
  }
  return -1;
}
// bitcasts where some elements' bytes are a NaN's: the other elements are exact (only a NaN element's use is
// not modelled)
int t_nan_lanes(int k) {
  v4si s = {0x7fc00001, 0x3f800000, 0x40000000, 0};
  volatile float zero = 0.0f;
  switch (k) {
  case 0: { v4sf f = (v4sf)s; return (int)(f[1] * 10); }
  case 1: { v4sf f = (v4sf)s; return (int)(f[2] + f[3]); }
  case 2: { v4sf a = {zero / zero, 1.0f, 2.0f, 3.0f}; v4si b = (v4si)a; return b[1] - b[3]; }
  }
  return -1;
}
// a bitcast giving a float element whose bits are a NaN's, then that element read: not modelled (Float has a
// single NaN), a NaN natively
int g_nan_cast() {
  volatile long long l = 0x7fc000003f800000LL;
  v2sf f = (v2sf)l;
  return f[1] != f[1];
}
