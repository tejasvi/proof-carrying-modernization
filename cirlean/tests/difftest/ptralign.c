/* Pointer conversions and alignment in C (C11 6.3.2.3p7: a pointer converted to a pointer to an object type that
   it is not correctly aligned for is undefined, whether or not it is used); run with CASES=ptralign_cases.txt,
   which describes the cases. A complete object counts as aligned for every type, as malloc's storage is. */
#include <stdlib.h>

/* an int pointer from a char pointer one byte into an int array (soundness audit M11), not used */
int a_misaligned_int(int k) {
  int a[2] = {1, 2};
  int *p = (int *)((char *)a + 1 + k);
  return p != 0;
}
/* an int pointer at byte 4 of the same array: element 1 */
int a_aligned_int(int k) {
  int a[2] = {1, 2 + k};
  int *p = (int *)((char *)a + 4);
  return *p;
}
/* a char pointer one byte in, through void * and back: neither type has an alignment above 1 */
int a_char_roundtrip(int k) {
  int a[2] = {1, 2};
  char *c = (char *)a + 1 + k;
  void *v = c;
  char *d = (char *)v;
  return d == c;
}
/* a short pointer at byte 2 of a char array */
int a_short_even(int k) {
  char buf[8] = {1, 2, 3, 4, 5, 6, 7, 8};
  short *p = (short *)(buf + 2 + 2 * k);
  return p != 0;
}
/* an int pointer one byte into malloc's storage */
int a_malloc_plus1(int k) {
  int *m = (int *)malloc(16);
  if (!m) return -1;
  int *p = (int *)((char *)m + 1 + k);
  int r = p != 0;
  free(m);
  return r;
}
/* an int pointer four bytes into malloc's storage, then used */
int a_malloc_plus4(int k) {
  int *m = (int *)malloc(16);
  if (!m) return -1;
  int *p = (int *)((char *)m + 4);
  *p = 7 + k;
  int r = m[1];
  free(m);
  return r;
}
/* a pointer to a structure of alignment 4 at byte 2 of an array of them */
struct S { int x; char c; };
int a_struct_odd(int k) {
  struct S arr[2] = {{1, 'a'}, {2, 'b'}};
  struct S *p = (struct S *)((char *)arr + 2 + k);
  return p != 0;
}
/* a double pointer at the double member of a structure, written through */
struct T { int i; int j; double d; };
int a_double_member(int k) {
  struct T t = {1, 2, 0.5};
  double *p = (double *)((char *)&t + 8);
  *p = 1.5 + k;
  return (int)(t.d * 2);
}
/* a double pointer four bytes into a double array */
int a_misaligned_double(int k) {
  double d[2] = {1.0, 2.0};
  double *p = (double *)((char *)d + 4 + k);
  return p != 0;
}
/* an int pointer one past the end of an int array, from a char pointer */
int a_one_past(int k) {
  int a[2] = {1, 2};
  int *p = (int *)((char *)a + 8 + k);
  return p == a + 2;
}
