/* sscanf's %i conversion (C11 7.21.6.2p12: the subject sequence of strtol in base 0) and the
   objects sscanf stores into: the one that a store of the program through the pointer reaches,
   such as a structure's first member through a pointer to the structure converted to the
   conversion's type (6.7.2.1p15), or a byte of an int for %hhu (6.5p7). A C source: sscanf is
   glibc's __isoc99_sscanf. */
#include <stdio.h>

static const char *ins[] = {
  "0x1F", "-0x10", "+017", "08", "0x", "0xg", "0X1f", " 12", "-", "0",
  "-0", "00", "0x7fffffff", "017777777777", "-2147483648", "0x1Fz", "0x-1", "- 5", "1e5", "0099",
  "0x80000000", "2147483648", "0b101", "0b"};

/* the value %i stores (-999 when nothing is assigned) */
int i_value(int which) {
  int v = -999;
  sscanf(ins[which], "%i", &v);
  return v;
}
/* the result and the characters consumed: r * 100 + n */
int i_count(int which) {
  int v = 0, n = -1;
  int r = sscanf(ins[which], "%i%n", &v, &n);
  return r * 100 + n;
}
/* with a field width of 2 */
int i_width2(int which) {
  int v = -999, n = -1;
  int r = sscanf(ins[which], "%2i%n", &v, &n);
  return r * 1000000 + n * 10000 + v;
}
/* length modifiers */
int i_hh(int k) {
  signed char c = 0;
  int r = sscanf(k ? "0x80" : "0x7f", "%hhi", &c);
  return r * 1000 + c;
}
int i_h(int k) {
  short s = 0;
  int r = sscanf(k ? "-0x8001" : "-0x8000", "%hi", &s);
  return r * 100000 + s;
}
int i_l(int k) {
  long l = 0;
  int r = sscanf("0x7fffffffffffffff", "%li", &l);
  return r * 10 + (l == 0x7fffffffffffffffL) + k;
}
/* %i needs a pointer to a signed integer: an unsigned int object is undefined */
int i_into_unsigned(int k) {
  unsigned u = 0;
  int r = sscanf("12", "%i", &u);
  return r * 100 + (int)u + k;
}
/* a pointer to a structure converted to int *: its first member */
struct S2 { int a, b; };
int s_struct_root_d(int k) {
  struct S2 s = {1, 2};
  int r = sscanf("40", "%d", (int *)&s);
  return r * 10000 + s.a * 100 + s.b + k;
}
int s_struct_root_i(int k) {
  struct S2 s = {1, 2};
  int r = sscanf("0x10", "%i", (int *)&s);
  return r * 10000 + s.a * 100 + s.b + k;
}
/* a structure whose first member is a structure */
struct Outer { struct S2 in; int c; };
int s_nested_root(int k) {
  struct Outer o = {{1, 2}, 3};
  int r = sscanf("7", "%d", (int *)&o);
  return r * 10000 + o.in.a * 100 + o.in.b * 10 + o.c + k;
}
/* a double first member through %lf */
struct DX { double d; int x; };
int s_struct_root_lf(int k) {
  struct DX s = {1.0, 3};
  int r = sscanf("2.5", "%lf", (double *)&s);
  return r * 1000 + (int)(s.d * 100) + s.x + k;
}
/* a two-dimensional array through int *: element [0][0] */
int s_array_root(int k) {
  int a[2][2] = {{1, 2}, {3, 4}};
  int r = sscanf("9", "%d", (int *)a);
  return r * 100000 + a[0][0] * 1000 + a[0][1] * 100 + a[1][0] * 10 + a[1][1] + k;
}
/* the first member is unsigned: %d needs an int (undefined, signedness counts) */
struct UX { unsigned u; int x; };
int s_struct_root_unsigned(int k) {
  struct UX s = {1, 2};
  int r = sscanf("5", "%d", (int *)&s);
  return r * 100 + (int)s.u + k;
}
/* %hhu into the bytes of an int (a character store, 6.5p7) */
int s_hhu_int_byte0(int k) {
  int x = 0x01020304;
  int r = sscanf("255", "%hhu", (unsigned char *)&x);
  return r * 0 + x + k;
}
int s_hhu_int_byte1(int k) {
  int x = 0x01020304;
  int r = sscanf("255", "%hhu", (unsigned char *)&x + 1);
  return r * 0 + x + k;
}
/* a union whose active member is an int, through int * */
union UI { int i; float f; };
int s_union_root(int k) {
  union UI u;
  u.i = 1;
  int r = sscanf("9", "%d", (int *)&u);
  return r * 100 + u.i + k;
}
