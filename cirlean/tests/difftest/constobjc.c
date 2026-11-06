/* Const-qualified local objects in C (run with CASES=constobj_cases.txt; constobj.cpp has
   the C++ cases): a const local of scalar, pointer or array type, or a structure of such
   members, is a read-only block that only its initialization writes (C11 6.7.3p6). The
   mb_* and q_* cases are rog's audit items M15 (n3mb.c, n3p7.c), as written there: Clang
   folds the read of c in them, c_store_read_ptr reads through the pointer. */
#include <setjmp.h>
#include <string.h>

int mb_const_local_store(int k) {
  const int c = 1;
  *(int *)&c = 5 + k;
  return c;
}
int mb_const_local_memcpy(int k) {
  const int c = 1;
  int v = 6 + k;
  memcpy((int *)&c, &v, sizeof v);
  return c;
}
struct CM { const int a; int b; };
int q_const_member_store(int k) {
  struct CM s = {1, 2};
  *(int *)&s.a = 5 + k;
  return s.a + s.b * 0;
}

int c_store_read_ptr(int k) {
  const int c = 1;
  int *volatile q = (int *)&c;
  *q = 5 + k;
  return *q;
}

static int f(int a) { return a + 40; }
struct S { int a; double b; int c[3]; };

int c_struct_read(int k) {
  const struct S s = {f(k), 2.5, {1, 2}};
  const struct S *volatile p = &s;
  return p->a + (int)p->b + p->c[1] + p->c[2];
}

int c_struct_mod(int k) {
  const struct S s = {f(k), 2.5, {1, 2}};
  int *volatile q = (int *)&s.c[2];
  *q = 7;
  return *q;
}

int c_struct_byte(int k) {
  const struct S s = {f(k), 2.5, {1, 2}};
  unsigned char *volatile q = (unsigned char *)&s.b;
  q[7] = 0;
  return s.a;
}

/* an int store through a pointer to the structure reaches its first member (6.7.2.1p15) */
int c_struct_start(int k) {
  const struct S s = {f(k), 2.5, {1, 2}};
  int *volatile q = (int *)&s;
  *q = 3;
  return *q;
}

int c_struct_copy(int k) {
  struct S t = {f(k), 2.5, {1, 2, 3}};
  const struct S s = t;
  const struct S *volatile p = &s;
  return p->a + p->c[2];
}

/* clang zero-fills the rows after the initialized ones with memset */
int c_rows(int k) {
  const int m[3][4] = {{f(k)}, {2, f(k + 2)}};
  const int (*volatile p)[4] = m;
  return p[0][0] + p[1][1] + p[2][3];
}

int c_memset_into(int k) {
  const int a[4] = {f(k), 2, 3, 4};
  void *volatile d = (void *)a;
  memset(d, 0, sizeof a);
  return a[1];
}

int c_memcpy_len0(int k) {
  const int a[2] = {k, 2};
  int b[2] = {5, 6};
  void *volatile d = (void *)a;
  memcpy(d, b, 0);
  return a[0];
}

/* a char store into a const int without initializer: C's UB; the model writes no byte into
   an indeterminate value, const or not */
int c_byte_noinit(int k) {
  const int x;
  unsigned char *volatile q = (unsigned char *)&x;
  q[0] = (unsigned char)k;
  return q[0];
}

/* the gaps: a const int without initializer takes a store as its initialization; CIR drops
   the const of a compound literal; a const union is not made read-only */
int c_gap_noinit(int k) {
  const int x;
  int *volatile q = (int *)&x;
  *q = k + 3;
  return *q;
}

int c_gap_compound_literal(int k) {
  const int *p = (const int[]){f(k), 2};
  int *volatile q = (int *)p;
  *q = 5;
  return *q;
}

union U { int i; float g; };
int c_gap_union(int k) {
  const union U u = {.i = k};
  int *volatile q = (int *)&u.i;
  *q = k + 8;
  return *q;
}

/* a backward goto and a longjmp run a declaration again, which initializes its object again
   (the const locals of such functions stay plain stack slots) */
int c_goto_back(int k) {
  int s = 0, i = 0;
again:;
  const int x = i * 10 + k;
  s += x;
  if (++i < 3) goto again;
  return s;
}

static jmp_buf jb;
int c_longjmp_back(int k) {
  volatile int n = 0;
  setjmp(jb);
  const int x = n * 10 + k;
  const int *volatile p = &x;
  if (++n < 3) longjmp(jb, 1);
  return *p;
}
