/* Conversions between integers and pointers (run with CASES=intptr_cases.txt). They are
   implementation-defined (C11 6.3.2.3p5, p6), and cirlean converts as GCC and Clang do, with flat
   addresses: a pointer converts to its address, an integer to the pointer into the live object
   whose range (one past its end included) holds it, which is what a round trip through
   uintptr_t needs (7.20.1.4p1) and what GCC requires of one ("the resulting pointer must
   reference the same object as the original pointer"). An integer that is no address of a live
   object converts to a pointer that compares by its address and designates nothing.
   Relational comparisons and arithmetic keep C's rules. Each case is labelled in the cases file. */
#include <setjmp.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

int i_roundtrip(int k) {
  int x = k + 4;
  uintptr_t u = (uintptr_t)&x;
  return *(int *)u;
}

struct S { int a, b; };

int i_roundtrip_member(int k) {
  struct S s = {k, k + 1};
  long v = (long)&s;
  return ((struct S *)v)->b;
}

int i_arith_in_object(int k) {
  int a[4] = {k, k + 1, k + 2, k + 3};
  int *p = (int *)((uintptr_t)&a[0] + sizeof(int));
  return *p;
}

/* pr58209: a pointer from integer arithmetic compared with the element pointer */
int i_eq_object(int k) {
  int a[4];
  int *p = (int *)((uintptr_t)&a[0] + k * sizeof(int));
  return p == &a[k];
}

int i_alignment(int k) {
  static int a[8] __attribute__((aligned(16)));
  return (int)(((uintptr_t)&a[k]) % 16) + (int)(((uintptr_t)&a[0]) % 16) * 100;
}

static int seven(void) { return 7; }

int i_function(int k) {
  uintptr_t u = (uintptr_t)&seven;
  int (*g)(void) = (int (*)(void))u;
  return g() + k + ((int (*)(void))u == &seven) * 10;
}

/* C11 6.5.8p5: the two pointers designate no object */
int i_relational_addr(int k) {
  char *p = (char *)0x10, *q = (char *)(uintptr_t)(0x20 + k);
  return p < q;
}

int i_tag_bit(int k) {
  long x = k + 8;
  uintptr_t t = (uintptr_t)&x | 1;
  long *p = (long *)(t & ~(uintptr_t)1);
  return (int)*p + (int)(t & 1);
}

int i_difference(int k) {
  int a[4];
  return (int)((uintptr_t)&a[k] - (uintptr_t)&a[0]);
}

int i_distinct(int k) {
  int a, b;
  uintptr_t x = (uintptr_t)&a, y = (uintptr_t)&b;
  return (x != y) + (x == (uintptr_t)&a) * 10 + k * 0;
}

int i_heap(int k) {
  int *h = malloc(4 * sizeof(int));
  h[2] = k + 5;
  uintptr_t u = (uintptr_t)h;
  int r = ((int *)u)[2];
  free(h);
  return r;
}

static uintptr_t dead_address(void) {
  int x = 3;
  return (uintptr_t)&x;
}

int i_dead_compare(int k) {
  int *p = (int *)dead_address();
  return (p != 0) + k * 0;
}

int i_dead_access(int k) {
  int *p = (int *)dead_address();
  return *p + k;
}

int i_one_past(int k) {
  int a[4];
  int *p = (int *)((uintptr_t)a + 4 * sizeof(int));
  return (p == a + 4) + k * 0;
}

int i_one_past_access(int k) {
  int a[4] = {1, 2, 3, 4};
  int *p = (int *)((uintptr_t)a + 4 * sizeof(int));
  return *p + k;
}

/* integer arithmetic that leaves the object: the result designates nothing */
int i_outside(int k) {
  int a[4] = {1, 2, 3, 4};
  int *p = (int *)((uintptr_t)a + 8 * sizeof(int));
  return *p + k;
}

int i_signed(int k) {
  int x = k;
  return (intptr_t)&x > 0;
}

int i_container_of(int k) {
  struct S s = {k + 2, k};
  uintptr_t ub = (uintptr_t)&s.b;
  struct S *o = (struct S *)(ub - offsetof(struct S, b));
  return o->a + (o == &s) * 10;
}

/* (uintptr_t) p % alignof for objects of every alignment the census uses, on the stack, in
   static storage and on the heap, and for members */
struct A16 { char c; double d; int i __attribute__((aligned(16))); };

int i_alignments(int k) {
  char c1;
  short s2;
  int i4;
  double d8;
  long double ld16;
  char a32[8] __attribute__((aligned(32)));
  char a64[8] __attribute__((aligned(64)));
  static char g1;
  static short g2;
  static double g8;
  static char g16[16] __attribute__((aligned(16)));
  static char g32[4] __attribute__((aligned(32)));
  static char g64[4] __attribute__((aligned(64)));
  struct A16 st;
  void *h = malloc(24), *h64 = 0;
  int bad = 0;
  bad += (uintptr_t)&c1 % _Alignof(char) != 0;
  bad += (uintptr_t)&s2 % _Alignof(short) != 0;
  bad += (uintptr_t)&i4 % _Alignof(int) != 0;
  bad += (uintptr_t)&d8 % _Alignof(double) != 0;
  bad += (uintptr_t)&ld16 % _Alignof(long double) != 0;
  bad += (uintptr_t)a32 % 32 != 0;
  bad += (uintptr_t)a64 % 64 != 0;
  bad += (uintptr_t)&g1 % 1 != 0;
  bad += (uintptr_t)&g2 % 2 != 0;
  bad += (uintptr_t)&g8 % 8 != 0;
  bad += (uintptr_t)g16 % 16 != 0;
  bad += (uintptr_t)g32 % 32 != 0;
  bad += (uintptr_t)g64 % 64 != 0;
  bad += (uintptr_t)&st % _Alignof(struct A16) != 0;
  bad += (uintptr_t)&st.d % 8 != 0;
  bad += (uintptr_t)&st.i % 16 != 0;
  bad += (uintptr_t)h % 16 != 0;
  if (posix_memalign(&h64, 64, 64) == 0) bad += (uintptr_t)h64 % 64 != 0;
  int off = (int)((uintptr_t)&st.i - (uintptr_t)&st);
  free(h);
  free(h64);
  return bad * 1000 + off + k * 0;
}

/* pr22098: a compound literal's element through uintptr_t */
int i_compound_literal(int k) {
  int a = k - 1;
  int *p;
  uintptr_t b = (uintptr_t)(p = &(int[]){0, 1, 2}[++a]);
  return *p * 10 + *(int *)b;
}

/* pr36339: a tagged pointer, one char past the object */
int i_tagged(int k) {
  uintptr_t heap[2] = {(uintptr_t)(42 + k), 0};
  uintptr_t tagged = (uintptr_t)(void *)((char *)heap + 1);
  uintptr_t *hp = (uintptr_t *)(void *)((char *)tagged - 1);
  return (int)hp[0] + (int)hp[1];
}

/* pr86231: integer constants against an object pointer */
int i_constants(int k) {
  static int v[8];
  void *p = &v[7];
  return (p == (void *)1) + (p == (void *)2) * 10 + ((void *)1 == (void *)(uintptr_t)k) * 100;
}

/* pr58209: foo (n) = (T *) ((T) foo (n - 1) + sizeof (T)) */
typedef intptr_t T;
static T tbuf[32];
static T *tfoo(T n) {
  if (n == 0) return tbuf;
  T s = (T)tfoo(n - 1);
  return (T *)(s + sizeof(T));
}

int i_recursive(int k) {
  int bad = 0;
  for (int i = 0; i < 27; i++) bad += tfoo(i) != tbuf + i;
  return bad + k * 0;
}

/* pr71626: a function's address as an integer, also in a vector */
typedef intptr_t V __attribute__((__vector_size__(sizeof(intptr_t))));

int i_function_vector(int k) {
  V v = {(intptr_t)seven};
  return (v[0] == (intptr_t)seven) + (v[0] != 0) * 10 + k * 0;
}

/* GNU C arithmetic on void * counts bytes (sizeof (void) is 1) */
int i_void_arith(int k) {
  struct S s = {k, k + 1};
  void *p = &s;
  void *q = p + 0, *r = p + sizeof(int);
  return (q == (void *)&s) + (r == (void *)&s.b) * 10 + *(int *)r * 100 + (int)(r - p) * 1000;
}

/* Lifetimes: an integer converts to a pointer into a live object only. An object whose
   lifetime has ended (6.2.4p2) is reached by no integer, whichever way it ended, and a later
   object never gets its address (natively it may). */

int i_freed_access(int k) {
  int *h = malloc(4 * sizeof(int));
  h[0] = k;
  uintptr_t u = (uintptr_t)h;
  free(h);
  return *(int *)u;
}

int i_realloc_stale(int k) {
  int *h = malloc(4 * sizeof(int));
  h[0] = k;
  uintptr_t u = (uintptr_t)h;
  int *g = realloc(h, 8 * sizeof(int));
  int r = *(int *)u;
  free(g);
  return r;
}

int i_scope_access(int k) {
  uintptr_t u;
  {
    int x = k + 2;
    u = (uintptr_t)&x;
  }
  return *(int *)u;
}

int i_loop_access(int k) {
  uintptr_t u = 0;
  int r = 0;
  for (int i = 0; i < 2; i++) {
    int x = k + i;
    if (i == 1) r = *(int *)u;
    u = (uintptr_t)&x;
  }
  return r;
}

static jmp_buf i_jb;
static uintptr_t i_saved;

static void i_jump_out(int k) {
  int x = k + 3;
  i_saved = (uintptr_t)&x;
  longjmp(i_jb, 1);
}

int i_longjmp_access(int k) {
  if (setjmp(i_jb) == 0) i_jump_out(k);
  return *(int *)i_saved;
}

int i_const_scope(int k) {
  uintptr_t u;
  {
    const int x = k + 40;
    u = (uintptr_t)&x;
  }
  return *(const int *)u;
}

int i_dead_reuse(int k) {
  return (dead_address() == dead_address()) + k * 0;
}

/* A pointer to an object whose lifetime has ended has an indeterminate value (6.2.4p2):
   converting it to an integer is undefined, as comparing it is. An address taken as an integer
   while the object lived stays an integer. */

static int *dead_pointer(void) {
  int x = 3;
  int *p = &x;
  return p;
}

int i_convert_freed(int k) {
  int *h = malloc(4 * sizeof(int));
  free(h);
  uintptr_t u = (uintptr_t)h;
  return (u != 0) + k * 0;
}

int i_convert_before_free(int k) {
  int *h = malloc(4 * sizeof(int));
  uintptr_t u = (uintptr_t)h;
  free(h);
  return (u != 0) + k * 0;
}

int i_convert_dead_local(int k) {
  uintptr_t u = (uintptr_t)dead_pointer();
  return (u != 0) + k * 0;
}

int i_convert_live_local(int k) {
  uintptr_t u = dead_address();
  return (u != 0) + k * 0;
}

int i_convert_null(int k) {
  int *p = 0;
  uintptr_t u = (uintptr_t)p;
  return (u == 0) + k * 0;
}

/* The same pointer in a condition: comparing it with null is undefined, but its conversion to
   a truth value (`if (p)`, `cir.cast(ptr_to_bool)`) is not caught, a known inconsistency. */

int i_bool_dead_local(int k) {
  int *p = dead_pointer();
  if (p) return 1 + k * 0;
  return k * 0;
}

int i_cmp_dead_local(int k) {
  int *p = dead_pointer();
  return (p != 0) + k * 0;
}
