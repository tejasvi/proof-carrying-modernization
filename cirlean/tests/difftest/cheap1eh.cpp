// Catch by pointer (run with MODE=status CASES=cheap1_cases.txt): the handler's parameter gets the
// thrown pointer when its type is the thrown pointer's type exactly. Expected result, labelled per
// case in the cases file: MATCH, or UB from cirrun (matching through a class hierarchy is not
// modelled).
struct A {
  int v;
};
struct B : A {
  int w;
};

int t_catch_ptr(int k) {
  static A a{7};
  try {
    throw &a;
  } catch (A *p) {
    return p->v + k;
  }
  return 0;
}
int t_catch_ptr_null(int k) {
  try {
    throw (int *)nullptr;
  } catch (int *p) {
    return p == nullptr ? 5 + k : 6 + k;
  }
  return 0;
}
int t_catch_ptr_heap(int k) {
  try {
    throw new A{9};
  } catch (A *p) {
    int v = p->v;
    delete p;
    return v + k;
  }
  return 0;
}
// a pointer to a derived class caught as a pointer to its base: not modelled
int t_catch_ptr_base(int k) {
  static B b;
  b.v = 3;
  try {
    throw &b;
  } catch (A *p) {
    return p->v + k;
  }
  return 0;
}
