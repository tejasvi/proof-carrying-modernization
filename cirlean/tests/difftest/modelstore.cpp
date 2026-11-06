// Library models that store into the caller's memory: the end pointer of
// strtol, strtoul, strtoll, strtoull, strtod and strtof (a char * stored
// through a char **), sscanf's conversion targets, and the guard variable of a
// static local. Each store is a typed store, checked like a store of the
// program (C11 6.5p7; 7.21.6.2p10-12 for sscanf: the object has exactly the
// conversion's type). ub_* cases are undefined, the rest are expected to match.
#include <cstdio>
#include <cstdlib>

struct S { int a; int b; };

// a char * stored into an int member: undefined (6.5p7); natively the 8-byte
// store also covers s.b
int ub_strtol_end_into_int(int k) {
  S s = {1, 2 + k};
  strtol("5", (char **)&s.a, 10);
  return s.b;
}
int ub_strtod_end_into_int(int k) {
  S s = {1, 2 + k};
  strtod("5", (char **)&s.a);
  return s.b;
}
// into a double member and into an int array element
int ub_strtoul_end_into_double(int k) {
  struct { double d; int z; } q = {1.5, 3 + k};
  strtoul("5", (char **)&q.d, 10);
  return q.z;
}
int ub_strtof_end_into_int_elem(int k) {
  int arr[3] = {1, 2, 3 + k};
  strtof("5", (char **)&arr[0]);
  return arr[2];
}
// into a char array: a pointer stored into char objects
int ub_strtoll_end_into_chars(int k) {
  char buf[16] = "abc";
  strtoll("5", (char **)buf, 10);
  return buf[10] + k;
}

// the end pointer into objects that hold a char *: a local, a struct member,
// cJSON's parse_number (unsigned char *after_end, cast to char **), an array
// element, a const char *; and no end pointer
int t_strtol_end_local(int k) {
  char *e = 0;
  const char *s = "123x";
  long v = strtol(s, &e, 10);
  return (int)v * 10 + (int)(e - s) + k;
}
int t_strtoull_end_member(int k) {
  struct { int z; char *e; } q = {7, 0};
  const char *s = "  0x1fz";
  unsigned long long v = strtoull(s, &q.e, 0);
  return (int)v * 100 + (int)(q.e - s) * 10 + q.z + k;
}
int t_strtod_parse_number(int k) {
  unsigned char number_c_string[8] = "2.5e1x";
  unsigned char *after_end = 0;
  double number = strtod((const char *)number_c_string, (char **)&after_end);
  return (int)number * 10 + (int)(after_end - number_c_string) + k;
}
int t_strtof_end_elem(int k) {
  char *ends[2] = {0, 0};
  const char *s = "1.5";
  float f = strtof(s, &ends[1]);
  return (int)(f * 10) * 10 + (int)(ends[1] - s) + (ends[0] == 0) * 1000 + k;
}
int t_strtoll_end_local(int k) {
  char *e = 0;
  const char *s = "-42 ";
  long long v = strtoll(s, &e, 10);
  return (int)v * 10 - (int)(e - s) + k;
}
int t_strtol_no_end(int k) { return (int)strtol("77", 0, 8) + (int)strtod("1.5", 0) * 100 + k; }

// sscanf: a conversion's object of another signedness or kind is undefined
// (7.21.6.2p10-12: %d needs a pointer to int, %x and %hhu pointers to unsigned
// int and unsigned char, %lf a pointer to double)
int ub_sscanf_d_into_unsigned(int k) {
  unsigned u = 7;
  int r = sscanf("5", "%d", &u);
  return r * 100 + (int)u + k;
}
int ub_sscanf_x_into_int(int k) {
  int i = 7;
  int r = sscanf("1f", "%x", &i);
  return r * 100 + i + k;
}
int ub_sscanf_hhu_into_signed_char(int k) {
  signed char c = 7;
  int r = sscanf("200", "%hhu", &c);
  return r * 1000 + c + k;
}
int ub_sscanf_lf_into_float(int k) {
  float f = 1.0f;
  int r = sscanf("2.5", "%lf", &f);
  return r * 100 + (int)f + k;
}
// each conversion into an object of its own type, in locals, a struct member
// and an array element; %n
int t_sscanf_own_types(int k) {
  int i = 0;
  unsigned u = 0, x = 0;
  signed char sc = 0;
  unsigned char uc = 0;
  long long ll = 0;
  double d = 0;
  float f = 0;
  int n = 0;
  int r = sscanf("-5 6 ff -7 200 -9000000000 2.5 1.25", "%d %u %x %hhd %hhu %lld %lf %f%n", &i, &u, &x, &sc, &uc,
                 &ll, &d, &f, &n);
  return r * 1000000 + (i + 10) * 100000 + (int)u * 10000 + (int)(x == 255) * 1000 + (sc + 10) * 100 +
         (uc == 200) * 10 + (ll == -9000000000LL) + (int)(d * 2) * 0 + (int)(f * 4) * 0 + n * 0 + k;
}
int t_sscanf_member_elem(int k) {
  S s = {0, 0};
  int arr[3] = {0, 0, 0};
  int r = sscanf("11 22", "%d %d", &s.b, &arr[2]);
  return r * 10000 + s.b * 100 + arr[2] + s.a + arr[0] + k;
}
// print_number's round trip: %lg into a local double
int t_sscanf_print_number(int k) {
  char buf[26] = "0.1";
  double test = 0.0;
  int r = sscanf(buf, "%lg", &test);
  return r * 1000 + (int)(test * 1000) + k;
}

// a static local with a dynamic initializer: the guard variable is acquired,
// then released by a typed store
static int compute(int k) { return k * 3 + 1; }
int t_guard(int k) {
  static int v = compute(k + 4);
  return v;
}
