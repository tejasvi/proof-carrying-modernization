// Union activation by stores (run with CASES=unionact_cases.txt, next to
// unionact_c.c): the member last stored is the active one, whichever pointer
// the store went through (C11 6.5.2.3p3, footnote 95), so a store through a
// member pointer formed earlier makes its member active and a read of another
// member reinterprets the stored bytes (a scalar of another size composed from
// them, little-endian); the common initial sequence of structs in a union may be
// read through either (6.5.2.3p6); a bit-field unit stored after another member
// keeps that member's bits; a member access of a const union writes nothing,
// and another member reads the initialized one. C++ modules read unions as C
// does (GCC and Clang document it; ISO C++ does not). From the soundness audits
// of next2 (core: U1, U2 and the related false UBs; library: F2, F3) and next3
// (NX1, NX2) plus controls. Expected result (labelled per case in the cases
// file): MATCH, or UB from cirrun where C leaves the value undefined or
// unspecified, or the bytes are not modelled (a NaN pattern), and one gap (an
// array member of a const union read through another array member).
#include <cstring>

union U { int i; float f; };

// U1: pointers formed first, then a float and an int stored: the int's bits read as a float
int u_stale_member(int k) {
  U u;
  int *pi = &u.i;
  float *pf = &u.f;
  *pf = 1.0f;
  *pi = 7 + k;
  return (int)(*pf * 1000.0f);
}

// U1: an int stored, a float stored through a pointer formed before, the int read
int u_stale_member_int(int k) {
  U u;
  u.i = 0;
  int *pi = &u.i;
  float *pf = &u.f;
  *pf = 1.0f + k;
  return *pi;
}

// U1: two integer members of one width
int u_stale_ints(int k) {
  union { int i; unsigned u; } x;
  int *pi = &x.i;
  unsigned *pu = &x.u;
  *pu = 5;
  *pi = 7 + k;
  return (int)*pu;
}

// U1: a read through a member pointer formed before another member was assigned
int u_old_ptr_read(int k) {
  U u;
  int *pi = &u.i;
  u.f = 2.0f + k;
  return *pi;
}

// U1 with a character pointer into a member formed before another member was
// stored: the byte of the stored int (6.5p7, 6.2.6.1p4)
int u_byte_old_ptr(int k) {
  U u;
  unsigned char *pc = (unsigned char *)&u.f;
  u.i = 0x01020304 + k;
  return pc[0];
}

// a character store through such a pointer: the stored int with its low byte
// replaced
int u_byte_store_old_ptr(int k) {
  U u;
  unsigned char *pc = (unsigned char *)&u.f;
  u.i = 0x01020304;
  pc[0] = (unsigned char)(0x10 + k);
  return u.i;
}

// the common initial sequence of two structs (6.5.2.3p6)
struct CA { int tag; int x; };
struct CB { int tag; float y; };
int u_common_initial(int k) {
  union { CA a; CB b; } u;
  u.a.tag = 3 + k;
  u.a.x = 1;
  return u.b.tag;
}

// past the common initial sequence: the int's bits read as a float (6.5.2.3p3)
int u_cis_other_member(int k) {
  union { CA a; CB b; } u;
  u.a.tag = 3;
  u.a.x = 0x40490fdb + k;
  return (int)(u.b.y * 1000.0f);
}

// a struct member written, a scalar member at the same offset and size read
int u_struct_then_int(int k) {
  union { struct { int x; int y; } s; int i; } u;
  u.s.x = 5 + k;
  u.s.y = 6;
  return u.i;
}

// a const union read through another member of the same size (no activation write)
int u_const_other_member(int k) {
  static const union { int i; float f; } cu = {.f = 1.0f};
  return cu.i + k;
}

// U2: a bit-field unit stored after a float member: the other bits are the float's
int u_bitfield_after_float(int k) {
  union { float f; struct { unsigned a : 3, b : 29; } s; } u;
  u.f = 1.0f + k;
  u.s.a = 1;
  return (int)u.s.b;
}

// U2: the same after an unsigned member of the unit's width
int u_bitfield_after_int(int k) {
  union { unsigned v; struct { unsigned a : 3, b : 29; } s; } u;
  u.v = 0xffffffffu - k;
  u.s.a = 1;
  return (int)u.s.b;
}

struct BS { unsigned a : 3, b : 29; };

// U2 through a pointer to the struct formed before the other member's store
int u_bitfield_old_ptr(int k) {
  union { unsigned v; BS s; } u;
  BS *ps = &u.s;
  u.v = 0xfffffff0u + k;
  ps->a = 1;
  return (int)ps->b;
}

// a union in a struct in an array, through a pointer formed before
int u_array_struct_member(int k) {
  struct W { int tag; U u; } w[2];
  w[0].tag = 0;
  w[1].tag = 1;
  int *pi = &w[1].u.i;
  w[1].u.f = 2.0f + k;
  return *pi + w[1].tag;
}

// a union inside a union: the inner members' reinterpretation
int u_nested(int k) {
  union { U in; long long ll; } o;
  o.in.f = 4.0f + k;
  return o.in.i;
}

// control: stores and reads through the same member pointers, no reinterpretation
int u_same_member(int k) {
  U u;
  int *pi = &u.i;
  float *pf = &u.f;
  *pf = 2.5f;
  float f = *pf;
  *pi = 7 + k;
  return *pi + (int)(f * 2.0f);
}

// F2: a const union read through its active first member, by a pointer (clang
// folds the direct read cu.i to 42, so here the member access stays)
static int first_member(const union U *p) { return p->i; }
int u_const_active(int k) {
  static const union U cu = {.i = 42};
  return first_member(&cu) + k;
}

// soundness audit F2: a const union at file scope read through its initialized
// member, which is not the first (forming the member pointer wrote the
// read-only block, which was refused: UB)
static const union U cu_member = {.f = 3.0f};
int u_const_init_member(int k) { return (int)cu_member.f + k; }

// soundness audit F3: a const union at file scope read through another member
static const union U cu_pun = {.f = 1.0f};
int u_const_global_pun(int k) { return cu_pun.i + k; }

// a table of const unions indexed at run time, read through the int member
int u_const_table(int k) {
  static const union U t[2] = {{.f = 1.0f}, {.i = 7}};
  return t[k].i;
}

// a bit-field of a const union whose unsigned member is initialized: the unit
// holds that member's bits
int u_const_bitfield(int k) {
  static const union { unsigned v; struct BS s; } cu = {.v = 0xffffffffu};
  return (int)cu.s.b + k;
}

// control: a const local union read through another member
int u_const_local_other(int k) {
  const union U cu = {.f = 1.0f};
  return cu.i + k;
}

// control: a store through another member of a const union modifies the const
// object (undefined, 6.7.3p6; natively a fault on read-only data)
int u_const_store_other(int k) {
  static const union U cu = {.f = 1.0f};
  ((union U *)&cu)->i = 5 + k;
  return ((union U *)&cu)->i;
}

// the gap: an array member of a const union read through another array member
// (C reads the floats' bits; an element access needs the member's array, and
// the read-only block holds the initialized member only)
int u_const_array_other(int k) {
  static const union { float f[2]; int a[2]; } cu = {.f = {1.0f, 2.0f}};
  return cu.a[k];
}

// control: a bool member read after a char member of another value (a trap representation in C)
int u_bool_trap(int k) {
  union { unsigned char c; bool b; } u;
  u.c = 2 + k;
  return u.b;
}

// control: a larger member than the one stored (its other bytes unspecified, 6.2.6.1p7)
int u_larger_member(int k) {
  union { short s; int i; } u;
  u.s = 5 + k;
  return u.i;
}

// control: a stale larger member through pointers formed first (unspecified high bytes)
int u_stale_larger(int k) {
  union { int i; long long ll; } u;
  long long *pll = &u.ll;
  int *pi = &u.i;
  *pll = 5;
  *pi = 7 + k;
  return (int)*pll;
}

// a struct member stored after a long long through an earlier pointer: the
// struct's members take the halves of the long long (4, the low half)
int u_split_scalar(int k) {
  union { struct { int a; int b; } s; long long ll; } u;
  int *pb = &u.s.b;
  u.ll = 0x500000004LL + k;
  *pb = 9;
  return u.s.a;
}

// C++ modules: a union member read reinterprets the active member's bytes, as GCC
// and Clang document; ISO C++ leaves it undefined ([class.union], [basic.life]p7);
// the common initial sequence is exempt in both
int x_cxx_inactive_read(int k) {
  union { int i; float f; } u;
  u.i = 0x3f800000 + k;
  return (int)(u.f * 10);
}
