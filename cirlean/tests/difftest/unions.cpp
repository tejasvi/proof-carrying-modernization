// Union type punning (run with CASES=unions_cases.txt): a store to one member
// of a union, then a read of another member, reinterprets the stored bytes (C11
// 6.5.2.3, footnote 95): a scalar of the same size directly, others composed
// from the bytes (6.5p7), aggregates member by member. Thrift c_glib's
// thrift_bitwise_cast_guint64 / thrift_bitwise_cast_gdouble are the
// double/uint64 case. Expected result (labelled per case in the cases file):
// MATCH on the t_* cases and on the aggregate controls; UB from cirrun on the
// pointer members (their bytes are not modelled), on a member larger than the
// one stored (its other bytes unspecified) and on the bits of a NaN (t_*_bits
// with a NaN pattern: `Float` keeps no NaN sign or payload), which the
// semantics leaves undefined (native runs print the GCC result).
#include <cstdint>

static uint64_t bitwise_cast_u64(double v) {
  union { double from; uint64_t to; } u;
  u.from = v;
  return u.to;
}

static double bitwise_cast_double(uint64_t v) {
  union { uint64_t from; double to; } u;
  u.from = v;
  return u.to;
}

static uint32_t bitwise_cast_u32(float v) {
  union { float from; uint32_t to; } u;
  u.from = v;
  return u.to;
}

static float bitwise_cast_float(uint32_t v) {
  union { uint32_t from; float to; } u;
  u.from = v;
  return u.to;
}

// double -> uint64: the bits of a / 8 + 0.5
int t_d2u64(int a) {
  return (int)(bitwise_cast_u64((double)a / 8 + 0.5) % 2147483647u);
}

// uint64 -> double: 2.0 plus a * 2^-11
int t_u642d(int a) {
  double d = bitwise_cast_double(0x4000000000000000ull + ((uint64_t)(unsigned)a << 40));
  return (int)(d * 1000);
}

// double -> uint64 -> double: the value back, its sign and exponent bits
int t_d_rt(int a) {
  double d = -(double)a / 3;
  double e = bitwise_cast_double(bitwise_cast_u64(d));
  return d == e ? (int)(bitwise_cast_u64(e) >> 52) : -1;
}

// uint64 -> double -> uint64 for an exponent field k (with the sign bit at
// 2048) and low fraction bits a (k = 0: subnormal or zero; k = 2047: infinity
// for a = 0, else a NaN)
int t_d_bits(int a, int k) {
  uint64_t b = ((uint64_t)(unsigned)k << 52) | (uint64_t)(unsigned)a;
  return (int)(bitwise_cast_u64(bitwise_cast_double(b)) % 2147483647u);
}

// float -> uint32: the bits of a * 0.25f - 1
int t_f2u32(int a) {
  return (int)(bitwise_cast_u32((float)a * 0.25f - 1) % 2147483647u);
}

// uint32 -> float: 1.0f plus a * 2^-11
int t_u322f(int a) {
  float f = bitwise_cast_float(0x3f800000u + (uint32_t)a * 4096u);
  return (int)(f * 100000);
}

// uint32 -> float -> uint32 for an exponent field k (with the sign bit at 256)
// and fraction bits a (k = 0: subnormal or zero; k = 255: infinity for a = 0,
// else a NaN)
int t_f_bits(int a, int k) {
  uint32_t b = ((uint32_t)k << 23) | ((uint32_t)a & 0x7fffffu);
  return (int)(bitwise_cast_u32(bitwise_cast_float(b)) % 2147483647u);
}

// int32 -> float: the int 0x3f800000 + a * 4096 (1.0f plus a * 2^-11; the
// sign bit for a = 524288 gives -1.0f)
int t_i2f(int a) {
  union { int32_t i; float f; } x;
  x.i = (int32_t)(0x3f800000u + (uint32_t)a * 4096u);
  return (int)(x.f * 100000);
}

// float -> int32: the bits of a / 3.0f - 2 (negative floats: negative ints)
int t_f2i(int a) {
  union { float f; int32_t i; } x;
  x.f = (float)a / 3 - 2;
  return x.i;
}

// int32 -> uint32
int t_i2u32(int a) {
  union { int32_t i; uint32_t u; } x;
  x.i = a;
  return (int)(x.u >> 1);
}

// uint32 -> int32
int t_u2i32(int a) {
  union { uint32_t u; int32_t i; } x;
  x.u = (uint32_t)a * 3u;
  return x.i;
}

// a 1-byte union: signed char -> unsigned char
int t_byte(int a) {
  union { signed char c; unsigned char u; } x;
  x.c = (signed char)a;
  return x.u;
}

// UB in the semantics: an int stored, a long long read (another size)
int u_int_ll(int a) {
  union { int i; long long ll; } x;
  x.i = a;
  return (int)(x.ll & 0x7fffffff);
}

// UB in the semantics: a float stored, a double read (another size)
int u_float_double(int a) {
  union { float f; double d; } x;
  x.f = (float)a;
  return x.d != 0;
}

// UB in the semantics: an int* stored, a uintptr_t read (pointer member)
int u_ptr_uintptr(int a) {
  union { int *p; uintptr_t u; } x;
  x.p = &a;
  return x.u != 0;
}

// UB in the semantics: a uintptr_t stored, an int* read (pointer member)
int u_uintptr_ptr(int a) {
  union { uintptr_t u; int *p; } x;
  x.u = (uintptr_t)a;
  return x.p == nullptr;
}

// a struct member written, a scalar member of the same size read (aggregate
// member): the long long composed from the two ints
int u_struct_ll(int a) {
  union { struct { int lo, hi; } s; long long ll; } x;
  x.s.lo = a;
  x.s.hi = 1;
  return (int)(x.ll & 0x7fffffff);
}

// a scalar written, a member of a struct member of the same size read
// (aggregate member): the long long's low half
int u_ll_struct(int a) {
  union { long long ll; struct { int lo, hi; } s; } x;
  x.ll = a;
  return x.s.lo;
}
