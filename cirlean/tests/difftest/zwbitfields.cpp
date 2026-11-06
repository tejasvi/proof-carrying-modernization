// Zero-width bit-fields (run with CASES=zwbitfields_cases.txt): `int : 0`
// starts the next bit-field at an allocation-unit boundary. CIR gives it a
// member without storage (`empty !cir.bitfield<[...]>`, zero bytes), which
// `#cir.const_record` initializers leave out. Expected result (labelled per
// case in the cases file): MATCH everywhere; the record sizes enter through
// malloc'd arrays and memcpy.
#include <cstdlib>
#include <cstring>

struct ZW {   // gcc.c-torture pr88904's S: c at offset 8, size 12
  unsigned a;
  unsigned b : 1;
  int : 0;
  unsigned c : 1;
};

struct ZW2 {  // y at offset 4
  char x;
  int : 0;
  char y;
};

struct ZW3 {  // zero-width bit-fields first, between and last
  int : 0;
  int v;
  long long : 0;
  signed char s : 3;
  short : 0;
  short w : 7;
  char : 0;
};

static ZW gz = {7, 1, 0};
static ZW2 gz2 = {'a', 'b'};
static ZW3 gz3 = {11, -2, 33};

int t_zw_fields(int v) {
  ZW z;
  z.a = v;
  z.b = v & 1;
  z.c = (v >> 1) & 1;
  return z.a * 100 + z.b * 10 + z.c;
}

static ZW make(int v) {
  ZW z = {5, 0, 1};
  z.a += v;
  return z;
}

int t_zw_init(int v) {
  ZW z = make(v);
  return z.a * 100 + z.b * 10 + z.c;
}

int t_zw_global(int v) {
  gz.c = v & 1;
  return gz.a * 100 + gz.b * 10 + gz.c + gz2.x * 1000 + gz2.y;
}

int t_zw_global3(int v) {
  gz3.w += v;
  return gz3.v * 10000 + gz3.s * 100 + gz3.w;
}

int t_zw_heap(int n) {
  ZW *p = (ZW *)malloc(n * sizeof(ZW));
  for (int i = 0; i < n; ++i) {
    p[i].a = i;
    p[i].b = i & 1;
    p[i].c = 1;
  }
  int s = 0;
  for (int i = 0; i < n; ++i) s += p[i].a * 4 + p[i].b * 2 + p[i].c;
  free(p);
  return s;
}

int t_zw_memcpy(int v) {
  ZW src = {0, 0, 0};
  src.a = v;
  src.c = 1;
  ZW dst;
  memcpy(&dst, &src, sizeof(ZW));
  ZW2 s2 = {'p', 'q'}, d2;
  memcpy(&d2, &s2, sizeof s2);
  return dst.a * 10 + dst.c + d2.y;
}

static ZW3 pass(ZW3 z, int v) {
  z.s = (signed char)(z.s + v);
  return z;
}

int t_zw_byvalue(int v) {
  ZW3 z = {1, 1, 1};
  ZW3 r = pass(z, v);
  return r.v * 1000 + r.s * 10 + r.w + (int)sizeof(ZW3);
}

int t_zw_sizes(int) {
  return (int)(sizeof(ZW) * 10000 + sizeof(ZW2) * 100 + sizeof(ZW3));
}
