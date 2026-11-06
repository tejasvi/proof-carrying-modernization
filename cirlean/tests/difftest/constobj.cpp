// Const-qualified local objects (run with CASES=constobj_cases.txt, which also has
// the C cases of constobjc.c): modifying an object defined with a const-qualified
// type is undefined (C11 6.7.3p6; C++ [dcl.type.cv]p4). A const local of scalar,
// pointer or array type (and in C a structure of such members) is a read-only block
// that only its initialization writes (`Op.allocaConst`); reads (of its bytes too),
// the initialization and writes through a cast of a pointer to const to a non-const
// object are defined, any other store into it (a char store into one of its bytes,
// a store of the value it holds) is undefined. Expected result (labelled per case in
// the cases file): MATCH, or UB from cirrun; the c_gap_* cases are the documented
// gaps (const parameters, const structure members, which CIR drops, and C++ class
// objects) and MATCH, as is c_scope: a const local outlives its region.
#include <cstring>

int c_mod_scalar(int a) {
  const int x = a + 5;
  int *volatile q = (int *)&x;
  *q = 9;
  return *q;
}

int c_read_scalar(int a) {
  const int x = a * 2;
  const int *volatile p = &x;
  return *p + 1;
}

int c_mod_array(int a) {
  const int arr[3] = {a, 2, 3};
  int *volatile q = (int *)arr;
  q[1] = 7;
  return q[1];
}

int c_read_array_partial(int a) {
  const int arr[4] = {a + 40, 2};
  const int *volatile p = arr;
  return p[0] + p[1] + p[3];
}

int c_loop(int a) {
  int s = 0;
  for (int i = 0; i < a; i++) {
    const int k = i * 2;
    const int *volatile p = &k;
    s += *p;
  }
  return s;
}

int c_ptr_to_const(int a) {
  int y = a;
  const int *p = &y;
  *(int *)p = 4;
  return y;
}

int c_const_ptr(int a) {
  int y = a, z = 2;
  int *const p = &y;
  int **volatile pp = (int **)&p;
  *pp = &z;
  return **pp;
}

static int set_param(const int n) {
  int *volatile q = (int *)&n;
  *q = 5;
  return *q;
}

int c_gap_param(int a) { return set_param(a); }

struct WithConstMember { const int x; int y; };

int c_gap_member(int a) {
  WithConstMember s = {a, 2};
  int *volatile q = (int *)&s.x;
  *q = 9;
  return *q;
}

struct Pair { int x, y; };

int c_gap_class(int a) {
  const Pair cs = {a, 2};
  Pair *volatile q = (Pair *)&cs;
  q->x = 9;
  return q->x;
}

int c_memcpy_into(int a) {
  const char s[4] = "abc";
  char *volatile d = (char *)s;
  memcpy(d, "xyz", 3);
  return d[0] + a;
}

int c_double(int a) {
  const double d = a + 0.5;
  double *volatile q = (double *)&d;
  *q = 2.5;
  return (int)(*q * 2);
}

int c_scope(int a) {
  const int *volatile p;
  {
    const int x = a;
    p = &x;
  }
  return *p;
}

int c_static_const(int a) {
  static const int s = 5;
  int *volatile q = (int *)&s;
  *q = a;
  return *q;
}

int c_constexpr(int a) {
  constexpr int k = 5;
  const int *volatile p = &k;
  return *p + a;
}

// the loop variables of a range-for: CIR hoists their allocas out of the loop and each
// iteration initializes them again (they stay plain stack slots)
int c_range_for(int a) {
  int arr[3] = {a, 2, 3};
  int s = 0;
  for (const int x : arr) s += x;
  for (const int &r : arr) s += 10 * r;
  return s;
}

int c_const_ref_temp(int a) {
  const int &r = a + 1;
  const int *volatile p = &r;
  return *p;
}

// clang zero-fills the rows after the initialized ones with a memset of each
// row, which the library model writes as the whole array (`Val.initBy`)
int c_init_rows(int a) {
  const int m[3][4] = {{a + 40}, {2, a + 2}};
  const int (*volatile p)[4] = m;
  return p[0][0] + p[1][1] + p[2][3];
}

int c_mod_filled_row(int a) {
  const int m[3][4] = {{a + 40}, {2, a + 2}};
  int *volatile q = (int *)&m[2][1];
  *q = 0;
  return *q + a;
}

int c_same_value(int a) {
  const int x = a + 5;
  int *volatile q = (int *)&x;
  *q = a + 5;
  return *q;
}

// a backward goto reaches the declaration again, which initializes the object
// again (the const objects of a function with a label stay plain stack slots)
int c_goto_back(int a) {
  int s = 0, i = 0;
again:;
  const int x = i * 10 + a;
  s += x;
  if (++i < 3) goto again;
  return s;
}

// the bytes of const objects (character accesses, C11 6.5p7): reads are
// defined; a char store into a determinate byte modifies the object
int c_byte_read(int a) {
  const int x = (a + 40) * 1000;
  const unsigned char *volatile p = (const unsigned char *)&x;
  return p[0] + p[1];
}

int c_byte_mod(int a) {
  const int x = a + 40;
  unsigned char *volatile q = (unsigned char *)&x;
  q[1] = 1;
  return x;
}

int c_byte_same(int a) {
  const int x = a + 40;
  unsigned char *volatile q = (unsigned char *)&x;
  q[0] = q[0];
  return x;
}

int c_byte_static(int a) {
  static const int g = 5;
  unsigned char *volatile q = (unsigned char *)&g;
  q[0] = (unsigned char)(a + 4);
  return g;
}

// a scalar store through a pointer to a const array reaches its element 0
int c_store_at_array(int a) {
  const int arr[2] = {a, 2};
  int *volatile q = (int *)&arr;
  *q = 3;
  return arr[0];
}
