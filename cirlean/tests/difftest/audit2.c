/* rog's audit items in C (a C source, run with CASES=audit2_cases.txt): M13, the missing value of
   a structure-returning function that reached its closing brace, used (C11 6.9.1p12: initializing
   or assigning an object, an argument, a return, a member access) or discarded; F12, memchr over
   the bytes of objects that are no character arrays (7.24.5.1, their representation as unsigned
   char, 6.2.6.1p4); the C11 rule of a compare-exchange's failure order, kept in C. Expected result,
   labelled per case in the cases file: MATCH, or UB from cirrun. */
#include <stdatomic.h>
#include <string.h>

struct P { int a, b; };
union U { int i; float f; };
struct A { int v[3]; };

/* the value is missing for k == 0 */
static struct P mk(int k) {
  if (k) {
    struct P p = {k, 2};
    return p;
  }
}
static union U mku(int k) {
  if (k) {
    union U u;
    u.i = k;
    return u;
  }
}
static struct A mka(int k) {
  if (k) {
    struct A s = {{k, 2, 3}};
    return s;
  }
}
/* returns from a loop, or reaches its closing brace when n <= 0 */
static struct P mkloop(int n) {
  for (int i = 0; i < n; i++)
    if (i == n - 1) {
      struct P p = {i, 1};
      return p;
    }
}
/* a present value with an indeterminate member */
static struct P mkpart(int k) {
  struct P p;
  p.a = k;
  return p;
}
static int take(struct P p) { return p.a + 1; }
static struct P again(int k) { return mk(k); }

int r_stored(int k) {
  struct P q = mk(k);
  (void)q;
  return 3;
}
int r_discarded(int k) {
  mk(k);
  return 4;
}
int r_void_cast(int k) {
  (void)mk(k);
  return 5;
}
int r_comma(int k) { return (mk(k), 6); }
int r_member(int k) { return mk(k).a + 7; }
int r_assigned(int k) {
  struct P q = {1, 1};
  q = mk(k);
  return q.a == 1 ? 8 : 9;
}
int r_passed(int k) { return take(mk(k)); }
int r_returned_again(int k) {
  again(k);
  return 10;
}
int r_union_stored(int k) {
  union U u = mku(k);
  (void)u;
  return 11;
}
int r_array_member_stored(int k) {
  struct A s = mka(k);
  (void)s;
  return 12;
}
int r_loop_discarded(int n) {
  mkloop(n);
  return 13;
}
int r_loop_stored(int n) {
  struct P p = mkloop(n);
  return p.a;
}
int r_partial_stored(int k) {
  struct P p = mkpart(k);
  return p.a;
}

/* memchr over an int array: found (byte 1 of a[1]), not found within n, past the array */
int m_int_array(int k) {
  int a[2] = {0x01020304, 0x05060708 + k};
  unsigned char *p = memchr(a, 0x06, sizeof a);
  return p ? (int)(p - (unsigned char *)a) : -1;
}
int m_int_array_not_found(int k) {
  int a[2] = {0x01020304, 0x05060708};
  return memchr(a, 0x05 + k, 4) == NULL;
}
int m_int_array_past(int k) {
  int a[2] = {0x01020304, 0x05060708};
  return memchr(a, 0x7f + k, 12) == NULL;
}
/* from the middle of an array, c converted to unsigned char (0x107 is 7) */
int m_long_array_mid(int k) {
  long a[3] = {1, 0x0706050403020100L + k, 2};
  unsigned char *p = memchr(&a[1], 0x107, 8);
  return p ? (int)(p - (unsigned char *)a) : -1;
}
/* a structure's bytes */
struct CS { char c; char d[3]; int x; };
int m_struct(int k) {
  struct CS s = {'a', {'b', 'c', 'd'}, 5 + k};
  char *p = memchr(&s, 'c', 4);
  return p ? (int)(p - (char *)&s) : -1;
}
/* a double's bytes: 1.0 is 0x3ff0000000000000, byte 6 is 0xf0 */
int m_double(int k) {
  double d = 1.0 + k;
  unsigned char *p = memchr(&d, 0xf0, sizeof d);
  return p ? (int)(p - (unsigned char *)&d) : -1;
}
/* the search reaches a padding byte (indeterminate) of struct PD before any match */
struct PD { char c; int x; };
int m_struct_padding(int k) {
  struct PD s;
  s.c = 'a';
  s.x = 0x01010101 + k;
  return memchr(&s, 0x7f, sizeof s) == NULL;
}
/* a union's bytes: not modelled */
int m_union(int k) {
  union U u;
  u.i = 0x01020304 + k;
  unsigned char *p = memchr(&u, 0x03, sizeof u);
  return p ? (int)(p - (unsigned char *)&u) : -1;
}

/* C11: a failure order stronger than the success order */
int x_cmpxchg_failure_stronger(int k) {
  atomic_int a = 1;
  int e = 1;
  _Bool ok = atomic_compare_exchange_strong_explicit(&a, &e, 2 + k, memory_order_relaxed, memory_order_seq_cst);
  return ok * 10 + atomic_load(&a);
}
/* control: the failure order no stronger */
int x_cmpxchg_failure_weaker(int k) {
  atomic_int a = 1;
  int e = 1;
  _Bool ok = atomic_compare_exchange_strong_explicit(&a, &e, 2 + k, memory_order_seq_cst, memory_order_acquire);
  return ok * 10 + atomic_load(&a);
}
