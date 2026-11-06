// Pointer comparison by address (run with CASES=ptreq_cases.txt): two pointers
// into the same complete object compare by the bytes they designate (C11
// 6.5.9p6, 6.5.8p5): a pointer to an object and one to the subobject at its
// beginning compare equal (6.7.2.1p15, p16: a structure and its first member, an
// array and its element 0, a union and its members), and so do the pointer one
// past an object and one to the object that follows it; pointers to members and
// elements of one object compare by their order in memory. Pointers into
// different objects stay unequal, and their relational comparison undefined.
// Expected result (labelled per case in the cases file): MATCH, or UB from cirrun
// (native runs print the GCC result).
#include <vector>

struct S { int a; int b; };
struct O { S in; int z; };
union U { int i; float f; };

// a structure and its first member
int q_struct_first(int k) {
  S s = {k, 2};
  return (static_cast<void *>(&s) == static_cast<void *>(&s.a)) * 10 + s.a;
}
// control: a structure and its second member
int q_struct_second(int k) {
  S s = {k, 2};
  return (static_cast<void *>(&s) == static_cast<void *>(&s.b)) * 10 + s.a;
}
// an array and its element 0
int q_array_first(int k) {
  int a[3] = {k, 2, 3};
  return (static_cast<void *>(&a) == static_cast<void *>(&a[0])) * 10 + a[0];
}
// a row of a two-dimensional array and its element 0
int q_row_first(int k) {
  int m[2][3] = {{1, 2, 3}, {k, 5, 6}};
  return (static_cast<void *>(&m[1]) == static_cast<void *>(&m[1][0])) * 10 + m[1][0];
}
// one past a row and the start of the next row
int q_past_row(int k) {
  int m[2][3] = {{1, 2, 3}, {k, 5, 6}};
  return (m[0] + 3 == &m[1][0]) * 10 + m[1][0];
}
// one past a member and the next member
int q_one_past_member(int k) {
  S s = {k, 2};
  return (&s.a + 1 == &s.b) * 10 + s.b;
}
// one past an array object (its pointer plus 1) and one past its last element
int q_array_object_end(int k) {
  int a[3] = {k, 2, 3};
  return (static_cast<void *>(&a + 1) == static_cast<void *>(a + 3)) * 10 + a[0];
}
// the members of a union
int q_union_members(int k) {
  U u;
  u.i = k;
  void *pi = &u.i;
  void *pf = &u.f;
  return (pi == pf) * 10 + 1;
}
// a char pointer at byte 4 of an int array and its element 1
int q_char_byte4(int k) {
  int a[2] = {k, 2};
  return ((char *)a + 4 == (char *)&a[1]) * 10 + a[1];
}
// the object from its member (container_of) and the object
int q_container_of(int k) {
  O o = {{k, 2}, 3};
  O *q = (O *)((char *)&o.z - 8);
  return (q == &o) * 10 + q->z;
}
// relational: elements of two rows, by address
int q_rel_rows(int k) {
  int m[2][3] = {{1, 2, 3}, {k, 5, 6}};
  return (&m[0][2] < &m[1][0]) * 100 + (&m[1][1] > &m[0][2]) * 10 + (m[0] + 3 <= &m[1][0]);
}
// relational: a member and the structure, as char pointers
int q_rel_members(int k) {
  S s = {k, 2};
  return ((char *)&s < (char *)&s.b) * 10 + (&s.a < &s.b) + s.a * 100;
}
// control: elements of one array
int q_rel_same_array(int k) {
  int a[3] = {1, 2, k};
  return (&a[0] < &a[2]) * 10 + (a + 3 > &a[1]);
}
// control: two objects compare unequal
int q_ne_objects(int k) {
  int x = k, y = 2;
  return (&x != &y) * 10 + x;
}
// control: the relational comparison of two objects is undefined
int q_rel_objects(int k) {
  int x = k, y = 2;
  return &x < &y;
}
// control: elements of a vector
int q_vector_elems(int k) {
  std::vector<int> v(3, k);
  return (&v[0] + 3 == v.data() + 3) * 10 + v[2];
}
// an atomic compare-exchange of a pointer compares addresses: the expected
// pointer to the structure equals the stored pointer to its first member
int q_cmpxchg_ptr(int k) {
  S s = {k, 2};
  int *slot = &s.a;
  int *expected = static_cast<int *>(static_cast<void *>(&s));
  bool ok = __atomic_compare_exchange_n(&slot, &expected, &s.b, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
  return ok * 10 + *slot;
}
