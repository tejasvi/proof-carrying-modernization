// Bit-fields whose storage unit is an array (run with CASES=bitfields_cases.txt).
// ClangIR gives a run of bit-fields whose width is not that of an integer type
// (8, 16, 32 or 64 bits) a storage unit of type !cir.array<!u8i x N>: in packed
// structs, before a member that limits the run, for wide fields and in unions.
// The bits of such a unit are numbered little-endian across its bytes. Expected
// result (labelled per case in the cases file): MATCH, except where the standard
// leaves the result undefined, or where a union member reads bytes that the active
// member does not hold (UB from cirrun).
#include <cstdlib>
#include <cstring>

struct __attribute__((packed)) P3 { unsigned a : 3; unsigned b : 13; unsigned c : 20; };   // u16, u8 x 3
struct __attribute__((packed)) P24 { unsigned a : 5; unsigned b : 17; unsigned c : 2; };   // u8 x 3
struct S5 { char tag; unsigned x : 20; unsigned y : 20; };                                   // s8, u8 x 3, u32
struct __attribute__((packed)) W40 { unsigned long long a : 40; unsigned long long b : 40; }; // u8 x 5, u8 x 5
struct W48 { unsigned long long a : 48; unsigned short s; };                                 // u8 x 6, u16
struct __attribute__((packed)) W120 { unsigned long long a : 7; unsigned long long b : 50; unsigned long long c : 63; };
struct __attribute__((packed)) SG { int a : 5; int b : 19; long long c : 41; unsigned char t; };
struct __attribute__((packed)) SO { unsigned a : 3; int b : 18; unsigned c : 3; };         // signed field at bit 3
struct __attribute__((packed)) BB { unsigned a : 23; bool f : 1; };                          // u8 x 3, with a bool
struct B8 { bool f : 1; bool g : 1; unsigned x : 6; };                                       // u8, with bools
enum Color { Red, Green, Blue, White };
struct __attribute__((packed)) EN { unsigned a : 22; Color c : 2; };
struct __attribute__((packed)) I100 { unsigned __int128 x : 100; unsigned char t; };
struct Cls {
  unsigned a : 12;
  unsigned b : 12;
  char tail;
  Cls(int x) : a(x), b(x * 2), tail(1) {}
  int sum() const { return a + b * 4096 + tail; }
};
struct Outer { int k; P3 in; short z; };
union U20 { unsigned a : 20; signed b : 20; };                                               // u8 x 3 | u8 x 3
union U3_21 { unsigned a : 3; signed b : 21; };                                              // u8 | u8 x 3
union U20i { unsigned a : 20; int i; };                                                      // u8 x 3 | s32
union UB3 { unsigned x : 20; unsigned char b[3]; };                                          // u8 x 3 | u8 x 3
struct HasU { char c; U20 u; char d; };
union U4 { unsigned a : 3; unsigned b : 5; };                                                // u8 | u8, padding
struct HasU4 { char c; U4 u; };

// fields spanning bytes in a packed struct: every field read after all writes
int t_packed(int n) {
  P3 p;
  p.a = n;
  p.b = n * 3;
  p.c = n * 7;
  return ((int)p.c * 31 + (int)p.b) * 8 + (int)p.a;
}

// fields at bit offsets 0, 5 and 22 of one 3-byte unit; a write keeps the other fields
int t_offsets(int n) {
  P24 p;
  p.a = n;
  p.b = n * 1000 + 7;
  p.c = n;
  int r = (int)p.a * 1000000 + (int)p.b * 4 + (int)p.c;
  p.b = 0x1ffff;
  return r ^ ((int)p.a + (int)p.c * 64 + (p.b == 0x1ffff ? 1 << 20 : 0));
}

// a 3-byte unit after a char, then a 4-byte one
int t_after_char(int n) {
  S5 s;
  s.tag = 'x';
  s.x = n * 4099;
  s.y = n;
  s.x += 1;
  return s.tag + (int)s.x * 2 + (int)s.y;
}

// two 40-bit fields, each in a 5-byte unit
int t_wide40(int n) {
  W40 w;
  w.a = (unsigned long long)n * 1000003ULL;
  w.b = ~0ULL - (unsigned long long)n;
  unsigned long long s = w.a + (w.b >> 8);
  return (int)(s % 1000000007ULL);
}

// a 48-bit field in a 6-byte unit before a short
int t_wide48(int n) {
  W48 w;
  w.a = ((unsigned long long)n << 32) | 0xdeadbeefULL;
  w.s = (unsigned short)n;
  return (int)((w.a >> 16) % 1000000007ULL) + w.s;
}

// 7 + 50 + 63 bits
int t_wide120(int n) {
  W120 w;
  w.a = n;
  w.b = (unsigned long long)n * 0x123456789ULL;
  w.c = ~(unsigned long long)n;
  unsigned long long s = w.a ^ w.b ^ (w.c >> 3);
  return (int)(s % 1000000007ULL);
}

// signed fields: sign extension on reads, values reduced modulo 2^width on writes (C++20)
int t_signed(int n) {
  SG s;
  s.a = n;
  s.b = -n * 1000;
  s.c = -(long long)n * 100000000LL;
  s.t = 9;
  return s.a * 1000 + s.b + (int)(s.c / 1000000) + s.t;
}

// a signed field that starts at bit 3 and spans all three bytes
int t_signed_mid(int n) {
  SO s;
  s.a = 5;
  s.b = -n;
  s.c = 6;
  int r = s.b * 100 + (int)s.a * 10 + (int)s.c;
  s.b = n * 5000;
  return r + s.b;
}

// a bool bit-field in a 3-byte unit
int t_bool_packed(int n) {
  BB b;
  b.a = n;
  b.f = (n & 1) != 0;
  int r = b.f ? 1000000 : 0;
  b.f = !b.f;
  return r + (b.f ? 2000000 : 0) + (int)b.a;
}

// bool bit-fields in a 1-byte unit
int t_bool_unit(int n) {
  B8 b;
  b.f = n > 3;
  b.g = n % 2;
  b.x = n;
  return (b.f ? 100 : 0) + (b.g ? 10 : 0) + (int)b.x * 1000;
}

// an enum bit-field
int t_enum(int n) {
  EN e;
  e.a = n;
  e.c = (Color)(n & 3);
  return (int)e.a * 4 + (int)e.c;
}

// a 100-bit field in a 13-byte unit
int t_int128(int n) {
  I100 b;
  b.x = ((unsigned __int128)(unsigned)n << 90) | (unsigned __int128)(unsigned)(n * 7);
  b.t = 3;
  return (int)(b.x >> 90) + (int)(b.x & 0xffffff) + b.t;
}

// a class with a constructor and a member function
int t_class(int n) {
  Cls c(n);
  c.b += 1;
  return c.sum();
}

// a packed struct as a member of another struct
int t_nested(int n) {
  Outer o;
  o.k = 1;
  o.z = 2;
  o.in.a = n;
  o.in.b = n + 1;
  o.in.c = n + 2;
  return o.k + o.z + (int)o.in.a + (int)o.in.b * 10 + (int)o.in.c * 100;
}

// union members with the same 3-byte storage unit: the bytes are reinterpreted
int t_union_same(int n) {
  U20 u;
  u.b = -n;
  return (int)u.a;
}

// union members read back without a reinterpretation
int t_union_member(int n) {
  U20 u;
  u.a = n;
  int r = (int)u.a;
  u.b = -n;
  return r * 2 + u.b;
}

// a 3-byte unit written, a 1-byte unit read: the first byte of the 3-byte unit
int u_union_size(int n) {
  U3_21 u;
  u.b = -n;
  return (int)u.a;
}

// a union member of another size: an int written, a 3-byte unit read (composed from
// the int's first three bytes)
int u_union_int(int n) {
  U20i u;
  u.i = n;
  return (int)u.a;
}

// a union with tail padding inside a struct, in a heap array (its size: new[] / sizeof)
int t_union_heap(int n) {
  HasU *h = new HasU[3];
  for (int i = 0; i < 3; i++) {
    h[i].c = (char)i;
    h[i].u.b = -n - i;
    h[i].d = (char)(i + 1);
  }
  int r = h[2].u.b + h[1].c * 10 + h[2].d * 100 + (int)h[0].u.a;
  delete[] h;
  return r;
}

// a union of 1-byte units with tail padding (integer storage) inside a struct, in a heap array
int t_union_unit(int n) {
  HasU4 *h = new HasU4[2];
  for (int i = 0; i < 2; i++) {
    h[i].c = (char)(i + 1);
    h[i].u.b = n + i;
  }
  int r = (int)h[1].u.a * 1000 + (int)h[1].u.b * 10 + h[1].c + (int)h[0].u.b;
  delete[] h;
  return r;
}

// a malloc'd array of packed structs
int t_heap_packed(int n) {
  P3 *p = (P3 *)std::malloc(sizeof(P3) * 4);
  for (int i = 0; i < 4; i++) {
    p[i].a = i;
    p[i].b = i * n;
    p[i].c = n - i;
  }
  int r = (int)p[3].c + (int)p[2].b * 3 + (int)p[1].a;
  std::free(p);
  return r;
}

static P3 mk(int n) {
  P3 p;
  p.a = n;
  p.b = n + 1;
  p.c = n + 2;
  return p;
}

static int take(P3 p) { return (int)p.c * 2 + (int)p.b; }

// copies: return by value, assignment, pass by value
int t_copy(int n) {
  P3 p = mk(n);
  P3 q;
  q = p;
  q.b = 7;
  return take(q) + (int)p.b;
}

P3 g_p3 = {5, 1000, 999999};

// initializers: a constant, a zero-initialized local, a global
int t_init(int n) {
  P3 p = {1, 2, 3};
  P3 z = {};
  p.c += n;
  z.b = n;
  g_p3.c = g_p3.c + n;
  return (int)(p.a + p.b + p.c + z.a + z.b + z.c + g_p3.a + g_p3.b) + (int)(g_p3.c % 1000);
}

// compound assignments and increments (unsigned fields wrap modulo 2^width)
int t_compound(int n) {
  P3 p = {};
  p.c = n;
  p.c += 5;
  p.c++;
  ++p.c;
  p.c *= 3;
  p.c |= 1;
  p.c ^= 0x80000;
  p.c >>= 1;
  p.b = n;
  p.b -= 9000;
  int old = p.c--;
  return old * 2 + (int)p.c + (int)p.b * 3;
}

// an array of structs and pointers to its elements
int t_array(int n) {
  P3 arr[4];
  for (int i = 0; i < 4; i++) {
    arr[i].a = i;
    arr[i].b = i * 100 + n;
    arr[i].c = n * i;
  }
  P3 *pp = &arr[2];
  pp->c += 1;
  return (int)pp->c + (int)arr[1].b + (int)arr[3].a + (int)(pp + 1)->b;
}

// memset and memcpy of a struct with a 3-byte unit
int t_memfns(int n) {
  P3 p;
  std::memset(&p, 0, sizeof p);
  p.c = n;
  P3 q;
  std::memcpy(&q, &p, sizeof p);
  return (int)q.a + (int)q.b + (int)q.c;
}

// a 3-byte unit and a byte array of the same type in a union: the bytes of the field
int t_union_bytes(int n) {
  UB3 u;
  u.x = n;
  int r = u.b[0] + u.b[1] * 1000 + u.b[2] * 1000000;
  u.b[1] = 0xff;
  return r + (int)u.x;
}

// a zero-initialized global read before any write
P3 g_zero;
int t_global_zero(int n) {
  int r = (int)g_zero.a + (int)g_zero.b + (int)g_zero.c;
  g_zero.c = n;
  return r + (int)g_zero.c;
}

static void bump(P3 *p, int k) {
  p->c += k;
  p->b ^= k;
}

// fields updated through a pointer in another function
int t_ptr_arg(int n) {
  P3 p = {7, 100, 1000};
  bump(&p, n);
  bump(&p, 3);
  return (int)p.a + (int)p.b + (int)p.c;
}

// a field whose storage unit was never written: an indeterminate value
int u_uninit(int n) {
  P3 p;
  p.a = n;
  return (int)p.c;
}
