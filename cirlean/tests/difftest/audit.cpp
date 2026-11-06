// Items of rog's audit of next3 (scratch/soundaudit_n3/FINDINGS.md): fflush of an input stream or of
// something that is no stream (M12), the typeinfo objects of the fundamental types (F5), typeinfo names
// read as strings (F6), what() returning one string per class (N1), vector left shifts wrapping (F15),
// memcmp's result as glibc's byte difference (N4).
#include <cstdio>
#include <cstring>
#include <exception>
#include <new>
#include <typeinfo>

typedef int v4si __attribute__((vector_size(16)));
typedef unsigned char v16qu __attribute__((vector_size(16)));

// fflush of the input stream stdin (C11 7.21.5.2p2: undefined)
int u_fflush_stdin(int k) { return fflush(stdin) + 10 + k; }
// fflush of something that is not a stream (7.1.4p1: undefined)
int u_fflush_not_stream(int k) {
  long x[8] = {0};
  x[0] = k;
  return fflush(reinterpret_cast<FILE *>(x)) + 10;
}
// fflush of the output streams and of a null pointer (all of them): 0
int t_fflush_out(int k) { return fflush(stdout) * 4 + fflush(stderr) * 2 + fflush(nullptr) + k; }

struct S {
  int a;
};
// typeid of fundamental types, of pointers to them and to const ones ([expr.typeid]p5: top-level
// cv-qualifiers are ignored), and of a class
int t_typeid(int k) {
  switch (k) {
  case 0: return typeid(int) == typeid(int);
  case 1: return typeid(const int) == typeid(int);
  case 2: return typeid(int) != typeid(double);
  case 3: return std::strcmp(typeid(int).name(), "i") == 0;
  case 4: return std::strcmp(typeid(int *).name(), "Pi") == 0;
  case 5: return std::strcmp(typeid(const char *).name(), "PKc") == 0;
  case 6: return (int)std::strlen(typeid(unsigned long long).name());
  case 7: { int x = 3; return typeid(x) == typeid(int); }
  case 8: return std::strcmp(typeid(S).name(), "1S") == 0;
  case 9: return (int)std::strlen(typeid(S).name());
  case 10: return typeid(S) == typeid(const S);
  case 11: return std::strcmp(typeid(bool).name(), "b") + std::strcmp(typeid(void).name(), "v");
  }
  return -1;
}
// what() twice on one object, and on two objects of the class: the same string
int t_what_same(int k) {
  std::exception e, f;
  std::bad_alloc g;
  switch (k) {
  case 0: return e.what() == e.what();
  case 1: return e.what() == f.what();
  case 2: return std::strcmp(g.what(), "std::bad_alloc") == 0 && g.what() == g.what();
  }
  return -1;
}
// vector left shifts wrap, as the other vector arithmetic (no overflow flags)
int t_vec_shl(int k) {
  v4si a = {-1, -2, 0x40000000, 0x7fffffff};
  v4si c = a << (v4si){1, 3, 1, 1};
  return c[k];
}
// a vector shift by the element width (undefined)
int u_vec_shl_count(int k) {
  v4si a = {1, 2, 3, 4};
  v4si c = a << (v4si){32, 0, 0, 0};
  return c[k];
}
// memcmp's result: glibc returns the difference of the first differing bytes, as unsigned char
int t_memcmp(int k) {
  unsigned char a[4] = {1, 2, 0x80, 4}, b[4] = {1, 4, 0x01, 4};
  char s[3] = "ab", t[3] = "ad";
  switch (k) {
  case 0: return std::memcmp(a, b, 4);
  case 1: return std::memcmp(a + 2, b + 2, 2);
  case 2: return std::memcmp(b, a, 4);
  case 3: return std::memcmp(s, t, 2);
  case 4: return std::memcmp(a, a, 4);
  }
  return -1;
}
