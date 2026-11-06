// The aggregate clause of C11 6.5p7 (run with CASES=aggclause_cases.txt; C's
// struct assignment, a cir.copy, is in aggclausec.c): an lvalue of a structure
// type whose members include the types of the objects it covers may access
// them. A structure of ints over an int member and the members after it, or
// over the elements of an int array, is read and written member by member, each
// member at its offset over the scalar there, and a member access through a
// pointer to such a structure places the member by bytes; a member that falls on
// no scalar of its type, or outside the object, is undefined. An access of a
// structure type to an object of another structure type stays undefined (6.5p7,
// audit G4). The r_* cases are the soundness audit's, with C's outcome. Expected
// result (labelled per case in the cases file): MATCH, or UB from cirrun (native
// runs print the GCC result).

struct S { int a; int b; };
struct P { int x; int y; };
struct T { int a; int b; };  // the layout of S, another type
struct F { float f; int y; };
struct Q { int a; int b; int c; };

// a structure of two ints stored over an int member and the next one (C++'s
// P::operator= assigns member by member)
int r_aggstore_member(int k) {
  S s = {1, 2};
  P p = {5 + k, 6};
  *(P *)&s.a = p;
  return s.b * 10 + s.a;
}
// the same over the elements of an int array
int r_aggstore_elem(int k) {
  int arr[2] = {1, 2};
  P p = {5 + k, 6};
  *(P *)arr = p;
  return arr[1] * 10 + arr[0];
}
// a structure of two ints read over an int member and the next one
int r_aggload_member(int k) {
  S s = {1 + k, 2};
  P p = *(P *)&s.a;
  return p.y * 10 + p.x;
}
// member accesses through a pointer to such a structure over an int array
int c_member_through(int k) {
  int arr[2] = {k, 7};
  P *pp = (P *)arr;
  return pp->y * 10 + pp->x;
}
// a structure of three ints read over elements 1 to 3 of an int array
int c_q_over_array(int k) {
  int arr[4] = {1, 2, 3, 4};
  Q q = *(Q *)&arr[1];
  return q.a * 100 + q.b * 10 + q.c + k;
}
// control: the second member falls outside the object
int u_agg_past_object(int k) {
  S s = {1, 2};
  P p = *(P *)&s.b;
  return p.y + k;
}
// control: a float member over an int
int u_agg_member_type(int k) {
  S s = {1, 2};
  F f = *(F *)&s.a;
  return f.y + k;
}
// control: a structure copy through another structure type (audit G4)
int u_copy_incompat(int k) {
  S s = {1 + k, 2};
  T t = *(T *)&s;
  return t.b;
}
