// Scalar accesses at the paths of aggregates (run with CASES=aggpath_cases.txt):
// a pointer to a structure, array or union, converted, points to its initial
// member, first element or each member (C11 6.7.2.1p15, p16), so a scalar access
// through it reaches the scalar the object starts with: a compatible type is an
// ordinary access, a character type one of its bytes (C11 6.5p7, 6.2.6.1p4),
// another type is type-punned (undefined). A scalar is never stored over the
// aggregate. An access of a record type to an object of another record type is
// undefined (6.5p7; C++ [basic.lval]p11), unless the object starts with a member
// of that type. A pointer to an array object used as a pointer to its element
// type points to element 0 (the e_* cases), and a lone object is an array of one
// in pointer arithmetic (C11 6.5.6p7, the l_* cases). The r_*, x_*, y_* and u_*
// cases are from the soundness audit of next2 (G5, G4), with C's outcome as the
// label. Expected result (labelled per case in the cases file): MATCH, or UB from
// cirrun (native runs print the GCC result).
#include <bitset>
#include <cstdlib>
#include <initializer_list>
#include <utility>
#include <vector>

struct S { int a; int b; };
struct T { int a; int b; };  // the layout of S, another type
struct O { S in; int z; };
union U { int i; float f; };

// a byte store through a pointer to a whole object changes the first byte of
// its first member; the other members and bytes stay
int r_bytestore_struct(int k) {
  S s = {0x12345678 + k, 2};
  *(unsigned char *)&s = 7;
  return *(int *)&s;
}
int r_bytestore_struct_b(int k) {
  S s = {0x12345678 + k, 2};
  *(unsigned char *)&s = 7;
  return s.b;
}
int r_bytestore_array(int k) {
  int arr[2] = {0x12345678 + k, 2};
  *(unsigned char *)&arr = 7;
  return *(int *)&arr;
}
int r_bytestore_nested(int k) {
  O o = {{0x12345678 + k, 2}, 3};
  *(unsigned char *)&o.in = 7;
  return *(int *)&o.in;
}
int x_heap_bytestore(int k) {
  S *h = (S *)malloc(sizeof(S));
  h->a = 0x12345678 + k;
  h->b = 2;
  *(unsigned char *)h = 7;
  int r = *(int *)h;
  free(h);
  return r;
}
int y_union_root_collapse(int k) {
  U u;
  u.i = 0x12345678 + k;
  *(unsigned char *)&u = 7;
  return *(int *)&u;
}
int u_bytestore_union(int k) {
  U u;
  u.i = 0x12345678 + k;
  *(unsigned char *)&u = 7;
  return u.i;
}
// a row of a two-dimensional array, through the row's address
int y_row_bytestore(int k) {
  int m[2][2] = {{0x12345678 + k, 2}, {3, 4}};
  *(unsigned char *)&m[0] = 7;
  return *(int *)&m[0];
}
// an int store through the address of the struct (of the row) is a store to
// its first member (element)
int r_intstore_struct_b(int k) {
  S s = {1, 2};
  *(int *)&s = 5 + k;
  return s.b;
}
int y_row_intstore_then_elem(int k) {
  int m[2][2] = {{1, 2}, {3, 4}};
  *(int *)&m[0] = 9 + k;
  return m[0][1];
}
// atomics through the struct's address operate on its first member
int x_atomic_fetch_root(int k) {
  S s = {1 + k, 2};
  return __atomic_fetch_add((int *)&s, 5, __ATOMIC_SEQ_CST) * 100 + s.a;
}
int x_atomic_xchg_root(int k) {
  S s = {1 + k, 2};
  int old = __atomic_exchange_n((int *)&s, 9, __ATOMIC_SEQ_CST);
  return old * 100 + s.a;
}
// a long long access over two int members: undefined (6.5p7)
int r_llstore_struct(int k) {
  S s = {1, 2};
  *(long long *)&s = 0x500000006LL + k;
  return (int)*(long long *)&s;
}
int r_llstore_array(int k) {
  int arr[2] = {1, 2};
  *(long long *)&arr = 0x500000006LL + k;
  return (int)*(long long *)&arr;
}
int r_atomic_llstore_struct(int k) {
  S s = {1, 2};
  __atomic_store_n((long long *)&s, 0x500000006LL + k, __ATOMIC_SEQ_CST);
  return (int)__atomic_load_n((long long *)&s, __ATOMIC_SEQ_CST);
}
// a float read of a struct whose first member is an int: type-punned
int a_float_of_struct(int k) {
  S s = {1065353216 + k, 2};
  return (int)*(float *)&s;
}
// a struct copy through another struct type: undefined (6.5p7)
int r_copy_incompat(int k) {
  S s = {1 + k, 2};
  T t = *(T *)&s;
  return t.b;
}
// control: a struct copy through a pointer to the object that starts with a
// member of that type (6.7.2.1p15)
int a_copy_initial_member(int k) {
  O o = {{1 + k, 2}, 3};
  S t = *(S *)&o;
  return t.a * 10 + t.b;
}
// control: a struct store through such a pointer
int a_store_initial_member(int k) {
  O o = {{1, 2}, 3};
  S t = {4 + k, 5};
  *(S *)&o = t;
  return o.in.a * 100 + o.in.b * 10 + o.z;
}
// control: a whole-struct copy of the same type
int a_copy_same(int k) {
  S s = {1 + k, 2};
  S t = *(S *)&s;
  return t.a * 10 + t.b;
}
// control: a char-wise copy of a struct into another of the same type
int a_bytecopy_struct(int k) {
  S s = {-123456 + k, 77};
  S t = {0, 0};
  unsigned char *d = (unsigned char *)&t;
  const unsigned char *p = (const unsigned char *)&s;
  for (unsigned i = 0; i < sizeof s; i++) d[i] = p[i];
  return t.a + t.b;
}

// a pointer to an array object, converted to a pointer to its element type,
// points to element 0, in pointer arithmetic and in accesses
// (std::initializer_list keeps its backing array so)
int e_array_object_stride(int k) {
  int a[3] = {10, 20 + k, 30};
  int (*pa)[3] = &a;
  int *p = (int *)pa;
  return p[1] + *(p + 2) + *p;
}
int e_init_list_ints(int k) {
  std::initializer_list<int> il = {10, 20 + k, 30};
  const int *b = il.begin();
  return b[1] + *(b + 2) + (int)(il.end() - il.begin());
}
int e_init_list_structs(int k) {
  std::initializer_list<S> il = {{1 + k, 2}, {3, 4}};
  S s = *il.begin();
  S t = il.begin()[1];
  return s.a * 100 + t.b * 10 + (int)il.size();
}
int e_array_object_record_load(int k) {
  S a[2] = {{1 + k, 2}, {3, 4}};
  S (*pa)[2] = &a;
  S s = *(S *)pa;
  return s.a * 10 + s.b;
}
// the end of the array reached from the array object and from its elements
int e_array_object_end(int k) {
  int a[3] = {1, 2 + k, 3};
  int *p = (int *)&a;
  int *e = p + 3;
  int n = 0;
  for (int *q = p; q != e; ++q) n = n * 10 + *q;
  return n;
}
// a range-for over an initializer_list of structs (its end compared with ==)
int e_init_list_iterate(int k) {
  std::initializer_list<S> il = {{1, 2}, {3, 4 + k}, {5, 6}};
  int s = 0;
  for (const S &e : il) s = s * 100 + e.a * 10 + e.b;
  return s;
}
// a vector of pairs built from an initializer_list
int e_vector_of_pairs(int k) {
  std::vector<std::pair<int, int>> v = {{7, 1}, {1, 5 + k}, {1, 3}};
  return v[1].second * 10 + v[2].first + (int)v.size() * 100;
}

// a lone object, no array element, as an array of one (C11 6.5.6p7)
int l_heap_one_past(int k) {
  int *h = (int *)malloc(sizeof(int));
  *h = k;
  int *e = h + 1;
  int r = (int)(e - h) * 10 + (e != h) + *h * 100;
  free(h);
  return r;
}
int l_heap_struct_one_past(int k) {
  S *h = (S *)malloc(sizeof(S));
  h->a = k;
  h->b = 2;
  S *e = h + 1;
  int n = 0;
  for (S *p = h; p != e; ++p) n += p->a + p->b;
  free(h);
  return n;
}
// a one-word member walked up to one past it (std::bitset's single word)
struct Bits { unsigned long w; };
int l_one_word_walk(int k) {
  Bits b = {5ul + (unsigned long)k};
  unsigned long sum = 0;
  for (unsigned long *p = &b.w; p != &b.w + 1; ++p) sum += *p;
  return (int)sum;
}
int l_bitset(int k) {
  std::bitset<32> bs((unsigned long)(5 + k));
  bs.set(7);
  return (int)bs.count() * 1000 + (int)(bs.to_ulong() % 1000);
}
// libc++'s growth from a one-element allocation (allocate(1), then
// __first_ + __cap, ++__end_, __end_ == __end_cap(), __end_ - __first_): heap
// storage of exactly one T is a lone object, and one past it, built as p + 1,
// as ++q and by char arithmetic, compares equal and subtracts to 1; p + 1 is
// not dereferenced
int l_one_elem_new(int k) {
  S *p = new S{k, 2};
  S *cap = p + 1;
  S *q = p;
  ++q;
  S *c = (S *)((char *)p + sizeof(S));
  int r = (q == cap) * 10000 + (c == cap) * 1000 + (int)(cap - p) * 100 + (int)(q - p) * 10 + p->b;
  delete p;
  return r;
}
// the same with a one-pointer allocation (std::deque's block map)
int l_one_elem_ptrs(int k) {
  int **p = new int *(nullptr);
  int **cap = p + 1;
  int **q = p;
  ++q;
  int r = (q == cap) * 100 + (int)(q - p) * 10 + (int)(cap - p) + k;
  delete p;
  return r;
}
