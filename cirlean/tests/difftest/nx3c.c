/* rog's L1 (a C source, run with CASES=nx3c_cases.txt): a structure with an array member returned
   by a call has temporary lifetime, which ends with the full expression or full declarator, and
   modifying it is undefined (C11 6.2.4p8). ClangIR marks no end of a full expression for such a
   temporary (its ref.tmp alloca is at the function's entry, in no scope), so cirlean keeps it alive
   to the end of the function: the use after the full expression and the modification are gaps.
   Expected result, labelled per case in the cases file: MATCH (the gaps included). */
struct A3 {
  int a[3];
};
static struct A3 mk3(int v) {
  struct A3 r = {{v, v + 1, v + 2}};
  return r;
}
int l_struct_temp_array_after(int k) {
  int *p = mk3(5 + k).a;
  return p[1];
}
int l_struct_temp_array_within(int k) { return mk3(5 + k).a[1]; }
int l_struct_temp_array_modify(int k) { return (mk3(5 + k).a[0] = 9); }
