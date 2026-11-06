// memcpy, memmove and memset over bytes (run with CASES=memb_cases.txt): between
// objects of different types, or over part of an object, they copy and set the
// bytes of the objects' representations (C11 7.24.2.1p2, 7.24.2.2p2, 7.24.6.1p2;
// 6.2.6.1p4), little-endian on our x86-64 targets. Expected result (labelled per
// case in the cases file): MATCH on the audit lines (r_, y_, b_) and the m_ cases,
// UB from cirrun on the u_ cases: overlapping memcpy, indeterminate bytes, a
// pointer not rebuilt from all its bytes in order, a bool trap representation, a
// NaN, a union (native runs print the GCC result).
#include <cstdlib>
#include <cstring>

struct S { int a; int b; };
struct T { int a; int b; };  // the layout of S, another type
struct O { S in; int z; };
struct BF { int a : 3; unsigned b : 5; int c : 1; };
struct Q { short a; short b; int c; };
struct P1 { char c; int i; };  // three bytes of padding after c
struct P2 { char d; int j; };
struct PA { int *p; int x; };
struct PB { int *q; int y; };
struct PP { int *p; int *q; };
struct PZ { int a; int *p; };  // four bytes of padding after a
union U { int i; float f; };

// the five audit lines (soundaudit_core: auditrec, audity, auditbf)

// memcpy of a whole struct from a struct of another type (34)
int r_memcpy_struct_other(int k) {
  S s = {1, 2};
  T t = {3 + k, 4};
  memcpy(&s, &t, sizeof s);
  return s.a * 10 + s.b;
}
// memcpy across two int members, from the first member's address (56)
int y_memcpy_into_member(int k) {
  S s = {1, 2};
  int src[2] = {5 + k, 6};
  memcpy(&s.a, src, sizeof src);
  return s.a * 10 + s.b;
}
// memcpy of an int array into a struct (56)
int y_memcpy_into_struct(int k) {
  S s = {1, 2};
  int src[2] = {5 + k, 6};
  memcpy(&s, src, sizeof src);
  return s.a * 10 + s.b;
}
// memset across two int members, from the first member's address (0)
int y_memset_member_span(int k) {
  S s = {1, 2};
  memset(&s.a, 0, sizeof s);
  return s.a + s.b + k;
}
// memset of a bit-field struct to all ones, then a signed field (-1)
int b_memset_ones(int k) {
  BF s;
  memset(&s, 0xff, sizeof s);
  return s.a + k;
}

// part of an object

// the low half of an int from a short
int m_low_half(int x) {
  int v = 0x11223344;
  short h = (short)x;
  memcpy(&v, &h, 2);
  return v;
}
// the high half of an int into a short, from a char pointer into the int
int m_high_half(int x) {
  int v = x;
  short h;
  memcpy(&h, (char *)&v + 2, 2);
  return h;
}
// four bytes across two int elements
int m_span_elems(int x, int k) {
  int a[2] = {0x11223344, 0x55667788};
  int b[2] = {x, x};
  memcpy((char *)b + 2, a, 4);
  return b[k];
}
// zero bytes 2 to 7 of an int array: half of a[0], all of a[1]
int m_memset_middle(int k) {
  int a[3] = {-1, -1, -1};
  memset((char *)a + 2, 0, 6);
  return a[k];
}
// eight bytes from a member's address: o.in.b and o.z
int m_struct_tail(int k) {
  O o = {{1, 2}, 3};
  int src[2] = {7 + k, 8};
  memcpy(&o.in.b, src, 8);
  return o.in.a * 100 + o.in.b * 10 + o.z;
}
// two bytes into the low half of a struct's second member
int m_member_low_bytes(int k) {
  S s = {1, 0x10000};
  unsigned char c[2] = {(unsigned char)(9 + k), 0};
  memcpy((char *)&s + 4, c, 2);
  return s.b;
}
// twelve bytes into an array of structs, from the middle of its first element
int m_array_of_structs(int k) {
  S arr[3] = {{1, 2}, {3, 4}, {5, 6}};
  int src[3] = {7, 8, 9};
  memcpy((char *)arr + 4, src, 12);
  return arr[k].a * 10 + arr[k].b;
}
// the first half of a struct into its second half (the same object, bytes that do not overlap)
int m_within_struct(int k) {
  S s = {5 + k, 6};
  memcpy((char *)&s + 4, &s, 4);
  return s.a * 10 + s.b;
}
// memmove between overlapping bytes of an int array (the source read first)
int m_overlap_memmove(int k) {
  int a[3] = {0x11223344, 0x55667788, 0x0a0b0c0d};
  memmove((char *)a + 2, a, 8);
  return a[k];
}

// objects of different types

// a struct's bytes into a char array
int m_struct_to_bytes(int k) {
  S s = {258, -2};
  unsigned char buf[8];
  memcpy(buf, &s, 8);
  return buf[k];
}
// a char array into an uninitialized struct
int m_bytes_to_struct(int k) {
  unsigned char buf[8] = {1, 0, 0, 0, (unsigned char)(2 + k), 0, 0, 0};
  S s;
  memcpy(&s, buf, 8);
  return s.a * 10 + s.b;
}
// a struct into a struct of another layout
int m_struct_layout(int k) {
  S s = {0x00020001, 3 + k};
  Q q;
  memcpy(&q, &s, 8);
  return q.a * 100 + q.b * 10 + q.c;
}
// chars into shorts
int m_chars_to_shorts(int k) {
  unsigned char b[4] = {1, 2, 3, 4};
  short s[2];
  memcpy(s, b, 4);
  return s[k];
}
// a long long into two ints
int m_ll_to_ints(int k) {
  long long v = 0x0000000700000005LL;
  int a[2];
  memcpy(a, &v, 8);
  return a[k];
}
// the bits of a double, through a long long
int m_double_bits(int x) {
  double d = x;
  long long v;
  memcpy(&v, &d, 8);
  return (int)(v >> 52);
}
// a double from the bits of a long long
int m_bits_double(int x) {
  long long v = 0x3FF8000000000000LL + x;
  double d;
  memcpy(&d, &v, 8);
  return (int)(d * 1000);
}
// the bits of a float, through an int
int m_float_bits(int x) {
  float f = (float)x;
  int i;
  memcpy(&i, &f, 4);
  return i;
}
// a float from the bits of an int
int m_bits_float(int x) {
  int i = 0x40490fdb ^ x;
  float f;
  memcpy(&f, &i, 4);
  return (int)(f * 1000);
}
// a bool from the byte 0 or 1
int m_bool_from_byte(int x) {
  unsigned char c = (unsigned char)x;
  bool b;
  memcpy(&b, &c, 1);
  return b ? 10 : 20;
}
// an int from the bytes of a string literal
int m_literal_to_int(int k) {
  int x;
  memcpy(&x, "abcd" + k, 4);
  return x;
}
// a malloc'd struct (typed at its cast) from an int array
int m_heap_struct(int k) {
  S *p = (S *)malloc(sizeof(S));
  int src[2] = {3, 4 + k};
  memcpy(p, src, 8);
  int r = p->a * 10 + p->b;
  free(p);
  return r;
}

// memset of other values than zero

// ints set to 0x01010101
int m_memset_ints(int k) {
  int a[2];
  memset(a, 1, sizeof a);
  return a[k];
}
// a large int array set to all ones
int m_memset_big(int k) {
  static int a[4096];
  memset(a, 0xff, sizeof a);
  return a[k] + a[4095 - k];
}
// a float set to the bytes 0x40 (3.0039...)
int m_memset_float(int k) {
  float f;
  memset(&f, 0x40, sizeof f);
  return (int)(f * 1000) + k;
}

// pointers

// a pointer member copied into a struct of another type: all its bytes, in order
int m_ptr_member(int k) {
  int v = 5 + k;
  PA a = {&v, 7};
  PB b;
  memcpy(&b, &a, sizeof b);
  return *b.q * 10 + b.y;
}
// two pointer members into a pointer array
int m_ptrs_to_array(int k) {
  int v0 = 3, v1 = 4;
  PP a = {&v0, &v1};
  int *arr[2];
  memcpy(arr, &a, sizeof arr);
  return *arr[k];
}
// zero bytes over a pointer member (and the padding before it): the null pointer
int m_null_by_bytes(int k) {
  int v = 1;
  PZ s;
  s.a = 7 + k;
  s.p = &v;
  memset((char *)&s + 4, 0, 12);
  return (s.p == nullptr) * 10 + s.a;
}

// padding

// a struct with padding into another struct type of that layout
int m_padding_copy(int k) {
  P1 a = {'x', 100 + k};
  P2 b;
  memcpy(&b, &a, sizeof b);
  return b.d + b.j;
}
// the bytes of a struct with padding, outside the padding (k = 0, 4..7)
int m_padding_bytes(int k) {
  P1 a;
  memset(&a, 0x55, sizeof a);
  a.c = 'x';
  a.i = 7;
  unsigned char buf[8];
  memcpy(buf, &a, 8);
  return buf[k];
}
// the bytes of a bit-field struct, whose padding is a member in ClangIR (k = 2, 3)
int m_bf_padding_bytes(int k) {
  BF s;
  memset(&s, 0xff, sizeof s);
  s.a = 1;
  unsigned char buf[4];
  memcpy(buf, &s, 4);
  return buf[k];
}

// undefined, or undefined in the model (the u_ cases)

// memcpy between overlapping bytes of an int array (C11 7.24.2.1p2)
int u_overlap_memcpy(int k) {
  int a[3] = {0x11223344, 0x55667788, 0x0a0b0c0d};
  memcpy((char *)a + 2, a, 8);
  return a[k];
}
// indeterminate bytes copied into an int: its value is indeterminate
int u_indeterminate_src(int k) {
  short h;
  int v = 5 + k;
  memcpy(&v, &h, 2);
  return v;
}
// half of an uninitialized int written: a partly initialized scalar is indeterminate in the model
int u_uninit_partial(int k) {
  int v;
  unsigned char c[2] = {1, (unsigned char)(2 + k)};
  memcpy(&v, c, 2);
  return v & 0xffff;
}
// half of a pointer copied: not all its bytes, in order (native: both pointers on the stack share their high half)
int u_ptr_half(int k) {
  int v = 5 + k, w = 6;
  int *p = &v, *q = &w;
  memcpy(&q, &p, 4);
  return *q;
}
// a pointer through a char buffer (gap: its bytes in a char array are indeterminate in the model)
int u_ptr_via_bytes(int k) {
  int v = 5 + k;
  int *p = &v, *q;
  unsigned char buf[sizeof p];
  memcpy(buf, &p, sizeof p);
  memcpy(&q, buf, sizeof q);
  return *q;
}
// a pointer's bytes into a long (an object pointer has no integer bytes in the model)
int u_ptr_to_long(int k) {
  int v = k;
  int *p = &v;
  long n;
  memcpy(&n, &p, sizeof n);
  return n != 0;
}
// a bool from the byte 2: a trap representation
int u_bool_trap(int k) {
  unsigned char c = (unsigned char)(2 + k);
  bool b;
  memcpy(&b, &c, 1);
  return b ? 10 : 20;
}
// a double set to all ones: a NaN, whose bytes are not modelled
int u_memset_nan(int k) {
  double d;
  memset(&d, 0xff, sizeof d);
  return (d != d) + k;
}
// a padding byte of a struct, after memset and member stores (C: unspecified values,
// 6.2.6.1p6; GCC keeps the memset's byte; padding outside the members has no storage in the model)
int u_padding_byte(int k) {
  P1 a;
  memset(&a, 0x55, sizeof a);
  a.c = 'x';
  a.i = 7;
  unsigned char buf[8];
  memcpy(buf, &a, 8);
  return buf[1 + k];
}
// a union's bytes: unions are not covered
int u_union_bytes(int k) {
  U u;
  u.i = 5 + k;
  int x;
  memcpy(&x, &u, sizeof x);
  return x;
}
