// Typeinfo objects (run with CASES=typeinfo_cases.txt): the `_ZTI…` globals
// (#cir.typeinfo: the type_info vtable pointer, the name, the bases and their
// offsets) are record constants, so the globals of classes with vtables and of
// thrown types are initialized, and `typeid(T) == typeid(U)` compares their
// name pointers (libc++'s unique implementation). Catch clauses match by
// typeinfo symbol, virtual calls read the vtable slots, and the typeid of a
// polymorphic object reads the typeinfo slot before the vtable's address
// point. Expected result (labelled per case in the cases file): MATCH on
// every case.
#include <typeinfo>

struct A {
  virtual int f() { return 1; }
  virtual ~A() {}
};

struct B : A {
  int f() override { return 2; }
};

struct M1 {
  virtual int g() { return 3; }
  virtual ~M1() {}
};

struct M2 {
  virtual int h() { return 4; }
  virtual ~M2() {}
};

struct MM : M1, M2 {
  int g() override { return 5; }
};

struct X {
  int v;
};

int t_vcall(int n) {
  B b;
  A &a = b;
  return a.f() * 10 + n;
}

int t_multi(int n) {
  MM m;
  M1 &a = m;
  return a.g() * 10 + m.h() + n;
}

int t_catch_class(int n) {
  try {
    throw X{n};
  } catch (X &x) {
    return x.v + 1;
  }
  return -1;
}

int t_catch_poly(int n) {
  B b;
  try {
    throw b;
  } catch (B &e) {
    return e.f() + n;
  }
  return -1;
}

int t_typeid_eq(int n) {
  return typeid(X) == typeid(X) ? n : -n;
}

int t_typeid_ne(int n) {
  return typeid(X) == typeid(A) ? -n : n;
}

int t_typeid_poly(int n) {
  B b;
  A &a = b;
  return typeid(a) == typeid(B) ? n : -n;
}
