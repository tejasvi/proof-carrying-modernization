/* Stores and loads of a vector type, and of a complex type, through pointers to objects of other types:
   elements of a float, int, unsigned or double array (also after a round trip through a char pointer, and
   on the heap), a structure of four floats; and the layout of records with vector members (run with
   CASES=vecstore_cases.txt). A vector type is T[N] in the model: such an access reads or writes the objects
   at its bytes, element by element, a record aligns a vector member as LLVM does, and a vector access whose
   stated alignment exceeds the element's needs a pointer aligned to it. Expected result (labelled per case in
   the cases file): MATCH, or UB from cirrun on the u_ cases. Native runs crash on a misaligned vector access
   (an aligned vector move) or print what the machine gives on the u_ cases. */
#include <complex.h>
#include <stdlib.h>
#include <string.h>

typedef float v4sf __attribute__ ((vector_size (16)));
typedef int v4si __attribute__ ((vector_size (16)));
typedef double v2df __attribute__ ((vector_size (16)));
typedef float v4sf_u __attribute__ ((vector_size (16), aligned (4)));
typedef float v8sf __attribute__ ((vector_size (32)));
typedef float v2sf __attribute__ ((vector_size (8)));

float buf[64];
int ibuf[16];
unsigned ubuf[16];
double dbuf[8];
float small[6];
struct F4 {
  float a, b, c, d;
} __attribute__ ((aligned (16)));
struct F4 f4;
struct Mixed {
  float a;
  int b;
  float c, d;
} __attribute__ ((aligned (16)));
struct Mixed mx;

/* m19 (intptr/micro, found by cjlemmas): through a char pointer and back */
int s_m19(int k) {
  buf[5] = 9;
  char *c = (char *) buf;
  float *d = (float *) c;
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) d = w;
  return (int) (buf[1] * 10 + buf[5]) + k;
}
int s_direct(int k) {
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) buf = w;
  return (int) (buf[0] * 1000 + buf[1] * 100 + buf[2] * 10 + buf[3]) + (int) buf[4] + k;
}
int s_elem4(int k) {
  buf[3] = 7;
  buf[8] = 6;
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) &buf[4] = w;
  return (int) (buf[3] * 10000 + buf[4] * 1000 + buf[5] * 100 + buf[6] * 10 + buf[7]) + (int) buf[8] * 100000 + k;
}
int s_local(int k) {
  float a[8] = {0};
  v4sf w = {5, 6, 7, 8};
  *(v4sf *) &a[4] = w;
  return (int) (a[3] * 1000 + a[4] * 100 + a[7]) + k;
}
int l_array(int k) {
  for (int i = 0; i < 8; ++i) buf[i] = (float) (i + 1);
  v4sf v = *(v4sf *) &buf[4];
  return (int) (v[0] * 1000 + v[1] * 100 + v[2] * 10 + v[3]) + k;
}
int l_char_roundtrip(int k) {
  buf[0] = 3;
  buf[1] = 4;
  buf[2] = 5;
  buf[3] = 6;
  char *c = (char *) buf;
  v4sf v = *(v4sf *) (float *) c;
  return (int) (v[0] + v[3] * 10) + k;
}
int s_loop(int k) {
  for (int i = 0; i < 16; ++i) buf[i] = (float) i;
  v4sf two = {2, 2, 2, 2};
  for (int i = 0; i < 16; i += 4) {
    v4sf v = *(v4sf *) &buf[i];
    *(v4sf *) &buf[i] = v * two;
  }
  float s = 0;
  for (int i = 0; i < 16; ++i) s += buf[i];
  return (int) s + k;
}
int s_struct(int k) {
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) &f4 = w;
  return (int) (f4.a * 1000 + f4.b * 100 + f4.c * 10 + f4.d) + k;
}
int l_struct(int k) {
  f4.a = 9;
  f4.b = 8;
  f4.c = 7;
  f4.d = 6;
  v4sf v = *(v4sf *) &f4;
  return (int) (v[0] * 1000 + v[1] * 100 + v[3]) + k;
}
int s_int(int k) {
  ibuf[3] = 9;
  v4si w = {5, 6, 7, 8};
  *(v4si *) &ibuf[4] = w;
  return ibuf[3] * 10000 + ibuf[4] * 1000 + ibuf[5] * 100 + ibuf[6] * 10 + ibuf[7] + k;
}
int s_int_over_unsigned(int k) {
  v4si w = {-1, 2, 3, 4};
  *(v4si *) ubuf = w;
  return (int) (ubuf[0] % 1000) + (int) ubuf[1] * 1000 + k;
}
int s_double(int k) {
  v2df w = {1.5, 2.5};
  *(v2df *) &dbuf[2] = w;
  return (int) (dbuf[2] * 10 + dbuf[3] * 100 + dbuf[1]) + k;
}
int s_unaligned_type(int k) {
  v4sf_u w = {1, 2, 3, 4};
  *(v4sf_u *) &buf[1] = w;
  return (int) (buf[0] * 10000 + buf[1] * 1000 + buf[2] * 100 + buf[3] * 10 + buf[4]) + k;
}
int s_heap(int k) {
  float *h = malloc(16 * sizeof (float));
  for (int i = 0; i < 16; ++i) h[i] = 0;
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) (h + 4) = w;
  int r = (int) (h[3] * 100 + h[4] * 10 + h[7]) + k;
  free(h);
  return r;
}
int s_complex(int k) {
  dbuf[2] = 5;
  double _Complex *z = (double _Complex *) dbuf;
  *z = 1.5 + 2.5 * I;
  return (int) (dbuf[0] * 10 + dbuf[1] * 100 + dbuf[2]) + k;
}
int l_complex(int k) {
  dbuf[2] = 3;
  dbuf[3] = 4;
  double _Complex z = *(double _Complex *) &dbuf[2];
  return (int) (creal(z) * 10 + cimag(z)) + k;
}
/* vector members: a record lays a vector out at a multiple of its size (rounded up to a power of two),
   which the bytes of the record show */
struct S {
  float x;
  v4sf v;
};
struct A {
  float x;
  v8sf v;
};
struct B {
  char c;
  v2sf v;
};
struct D {
  float x;
  v4sf arr[2];
  float y;
};
struct N {
  char c;
  struct S s;
};
union U {
  v4sf v;
  float f[4];
};
struct W {
  float x;
  union U u;
};
int r_member16(int k) {
  struct S s = {0};
  s.v = (v4sf){1, 2, 3, 4};
  float f;
  memcpy(&f, (unsigned char *) &s + 16, sizeof f);
  return (int) f * 10 + (int) sizeof s + k;
}
int r_member_copy(int k) {
  struct S s = {0};
  s.v = (v4sf){5, 6, 7, 8};
  struct S t;
  memcpy(&t, &s, sizeof s);
  return (int) t.v[2] + k;
}
int r_member32(int k) {
  struct A a = {0};
  a.v[0] = 3;
  float f;
  memcpy(&f, (unsigned char *) &a + 32, sizeof f);
  return (int) f + (int) sizeof a + k;
}
int r_member8(int k) {
  struct B b = {0};
  b.v[1] = 7;
  float f;
  memcpy(&f, (unsigned char *) &b + 12, sizeof f);
  return (int) f + (int) sizeof b + k;
}
int r_member_array(int k) {
  struct D d = {0};
  d.arr[1][2] = 9;
  d.y = 4;
  float f, g;
  memcpy(&f, (unsigned char *) &d + 40, sizeof f);
  memcpy(&g, (unsigned char *) &d + 48, sizeof g);
  return (int) (f * 10 + g) + (int) sizeof d + k;
}
int r_member_nested(int k) {
  struct N n = {0};
  n.s.v[3] = 6;
  float f;
  memcpy(&f, (unsigned char *) &n + 44, sizeof f);
  return (int) f + (int) sizeof n + k;
}
int r_member_union(int k) {
  struct W w = {0};
  w.u.f[1] = 5;
  float f;
  memcpy(&f, (unsigned char *) &w + 20, sizeof f);
  return (int) f + (int) sizeof w + k;
}
/* offsets and sizes as the model lays the records out: differences of char pointers */
int r_offset16(int k) {
  struct S s;
  return (int) ((char *) &s.v - (char *) &s) + k;
}
int r_offset32(int k) {
  struct A a;
  return (int) ((char *) &a.v - (char *) &a) + k;
}
int r_offset8(int k) {
  struct B b;
  return (int) ((char *) &b.v - (char *) &b) + k;
}
int r_size_array(int k) {
  struct S arr[2];
  return (int) ((char *) &arr[1] - (char *) &arr[0]) + k;
}
int r_offset_after_array(int k) {
  struct D d;
  return (int) ((char *) &d.y - (char *) &d) * 100 + (int) ((char *) &d.arr[1] - (char *) &d) + k;
}
int r_offset_nested(int k) {
  struct N n;
  return (int) ((char *) &n.s.v - (char *) &n) + k;
}
/* undefined: the vector's last elements are past the end of the array */
int u_past_end(int k) {
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) &small[4] = w;
  return (int) small[5] + k;
}
/* undefined in C: a vector pointer at a byte offset where no float starts (C11 6.3.2.3p7) */
int u_misaligned_bytes(int k) {
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) ((char *) buf + 2) = w;
  return (int) buf[1] + k;
}
/* undefined (C11 6.5p7): the vector's second element is an int object */
int u_struct_mixed(int k) {
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) &mx = w;
  return mx.b + k;
}
/* undefined: a vector read of elements never written (indeterminate) */
int u_load_uninit(int k) {
  float a[4];
  a[0] = 1;
  v4sf v = *(v4sf *) a;
  return (int) v[0] + k;
}
/* undefined (C11 6.3.2.3p7): a vector store through a pointer aligned for float, not for the vector */
int u_misaligned_vector(int k) {
  v4sf w = {1, 2, 3, 4};
  *(v4sf *) &buf[1] = w;
  return (int) buf[1] + k;
}
/* undefined (C11 6.3.2.3p7): a vector load through a pointer aligned for float, not for the vector */
int u_misaligned_load(int k) {
  for (int i = 0; i < 8; ++i) buf[i] = (float) i;
  v4sf v = *(v4sf *) &buf[2];
  return (int) v[0] + k;
}
