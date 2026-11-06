// Copies between overlapping objects (run with CASES=overlap_cases.txt): memcpy,
// strcpy, sprintf and snprintf leave them undefined (C11 7.24.2.1p2, 7.24.2.3p2,
// 7.21.6.6p2, 7.21.6.5p2); memmove copies them. Expected result (labelled per
// case in the cases file): UB from cirrun on the t_ub_* cases (native runs print
// glibc's result), MATCH on the t_ok_* cases.
#include <cstdio>
#include <cstring>

static int sum8(const int *a) {
  int s = 0;
  for (int i = 0; i < 8; i++) s = s * 3 + a[i];
  return s;
}

// UB: memcpy(a + 1, a, 4 * sizeof(int)) on int a[8] (elements [0, 4) and [1, 5))
int t_ub_memcpy_shift(int k) {
  int a[8];
  for (int i = 0; i < 8; i++) a[i] = i + k;
  memcpy(a + 1, a, 4 * sizeof(int));
  return sum8(a);
}

// UB: memcpy(&s, &s, sizeof s), a struct onto itself
int t_ub_memcpy_self(int k) {
  struct S { int x, y; } s = {k, 2 * k};
  memcpy(&s, &s, sizeof s);
  return s.x + s.y;
}

// UB: memcpy between two members of one union (the same storage)
int t_ub_memcpy_union(int k) {
  union { int a; int b; } u;
  u.a = k;
  memcpy(&u.b, &u.a, sizeof(int));
  return u.b;
}

// UB: strcpy(buf + 2, buf), the string and its copy overlap
int t_ub_strcpy(int k) {
  char buf[16] = "abcdef";
  buf[0] = (char)('a' + k);
  strcpy(buf + 2, buf);
  return (int)strlen(buf);
}

// UB: sprintf(buf, "%s!", buf), the %s argument is the destination
int t_ub_sprintf(int k) {
  char buf[32] = "xyz";
  buf[1] = (char)('a' + k);
  sprintf(buf, "%s!", buf);
  return (int)strlen(buf);
}

// UB: snprintf(buf + 1, 8, "%s", buf), the %s argument overlaps the destination
int t_ub_snprintf(int k) {
  char buf[32] = "pqrs";
  buf[0] = (char)('a' + k);
  snprintf(buf + 1, 8, "%s", buf);
  return (int)strlen(buf);
}

// memmove(a + 1, a, 4 * sizeof(int)): overlapping, forward
int t_ok_memmove_fwd(int k) {
  int a[8];
  for (int i = 0; i < 8; i++) a[i] = i + k;
  memmove(a + 1, a, 4 * sizeof(int));
  return sum8(a);
}

// memmove(a, a + 1, 4 * sizeof(int)): overlapping, backward
int t_ok_memmove_bwd(int k) {
  int a[8];
  for (int i = 0; i < 8; i++) a[i] = i + k;
  memmove(a, a + 1, 4 * sizeof(int));
  return sum8(a);
}

// memcpy(a + 4, a, 4 * sizeof(int)): adjacent slices [0, 4) and [4, 8) of one array
int t_ok_memcpy_adjacent(int k) {
  int a[8];
  for (int i = 0; i < 8; i++) a[i] = i + k;
  memcpy(a + 4, a, 4 * sizeof(int));
  return sum8(a);
}

// memcpy(p, p, 0): nothing is copied
int t_ok_memcpy_zero(int k) {
  int a[8];
  for (int i = 0; i < 8; i++) a[i] = i + k;
  memcpy(a, a, 0);
  return sum8(a);
}

// memcpy between two array members of one struct
int t_ok_memcpy_members(int k) {
  struct T { int a[4]; int b[4]; } t;
  for (int i = 0; i < 4; i++) { t.a[i] = i + k; t.b[i] = 0; }
  memcpy(t.b, t.a, sizeof t.a);
  return t.b[0] + t.b[3] * 10;
}

// strcpy(buf + 8, buf): disjoint parts of one array
int t_ok_strcpy(int k) {
  char buf[32];
  strcpy(buf, "hi");
  buf[1] = (char)('a' + k);
  strcpy(buf + 8, buf);
  return buf[8] * 100 + buf[9];
}

// sprintf(buf + 8, "%s-%d", buf, k): the %s argument is a disjoint part of the destination's array
int t_ok_sprintf(int k) {
  char buf[32] = "abc";
  sprintf(buf + 8, "%s-%d", buf, k);
  return (int)strlen(buf + 8) * 100 + buf[12];
}
