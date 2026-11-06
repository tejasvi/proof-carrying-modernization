// rog's NX3 (run with CASES=nx3_cases.txt): an object's lifetime ends when its destructor call
// starts (C++ [basic.life]p1), so once the destructor has run, reading the object is undefined
// ([basic.life]p7), until its storage is reused ([basic.life]p8: a placement new). The destroyed
// object: a by-value parameter (the caller's temporary, destroyed at the end of the caller's full
// expression), a temporary bound to a reference parameter, and objects destroyed by an explicit
// destructor call (automatic, a member, an array element, on the heap, of a derived class, const,
// with virtual bases). A temporary without a destructor (rog's L2: an initializer_list's backing
// array) has no end of its full expression in ClangIR and stays alive: a gap. Expected result,
// labelled per case in the cases file: MATCH (the gaps included), or UB from cirrun.
#include <initializer_list>
#include <new>

struct S {
  int x;
  S(int v) : x(v) {}
  S(const S &o) : x(o.x) {}
  ~S() { x = -1; }
};
static int *gp;
static int take(S s) {
  gp = &s.x;
  return 0;
}
static const int *getx(const S &s) { return &s.x; }

// by-value parameters and temporaries
int x_byval_param_after(int k) {
  take(S(5 + k));
  return *gp;
}
int x_byval_param_in_full_expr(int k) { return (take(S(5 + k)), *gp); }
int x_temp_after_full_expr(int k) {
  const int *q = getx(S(5 + k));
  return *q;
}
int x_temp_in_full_expr(int k) { return *getx(S(5 + k)); }
// a temporary bound to a local reference lives as long as the reference ([class.temporary]p6)
int x_temp_extended(int k) {
  const S &r = S(5 + k);
  return r.x;
}

// explicit destructor calls
int x_after_explicit_dtor(int k) {
  S s(5 + k);
  s.~S();
  int r = s.x;
  new (&s) S(7);
  return r;
}
int x_reuse_after_explicit_dtor(int k) {
  S s(5 + k);
  s.~S();
  new (&s) S(7 + k);
  return s.x;
}
int x_read_before_explicit_dtor(int k) {
  S s(5 + k);
  int r = s.x;
  s.~S();
  new (&s) S(1);
  return r;
}
struct O {
  S m;
  int t;
};
int x_member_after_dtor(int k) {
  O o{S(5 + k), 3};
  o.m.~S();
  int r = o.m.x;
  new (&o.m) S(1);
  return r;
}
int x_other_member_after_dtor(int k) {
  O o{S(5 + k), 3 + k};
  o.m.~S();
  int r = o.t;
  new (&o.m) S(1);
  return r;
}
int x_element_after_dtor(int k) {
  S a[2] = {S(1 + k), S(2 + k)};
  a[1].~S();
  int r = a[1].x;
  new (&a[1]) S(3);
  return r;
}
int x_other_element_after_dtor(int k) {
  S a[2] = {S(1 + k), S(2 + k)};
  a[1].~S();
  int r = a[0].x;
  new (&a[1]) S(3);
  return r;
}
int x_heap_after_dtor(int k) {
  S *p = new S(5 + k);
  p->~S();
  int r = p->x;
  ::operator delete(p);
  return r;
}
int x_heap_reuse(int k) {
  S *p = new S(5 + k);
  p->~S();
  new (p) S(9 + k);
  int r = p->x;
  delete p;
  return r;
}
struct D : S {
  int d;
  D(int v) : S(v), d(2 * v) {}
  ~D() { d = -2; }
};
int x_derived_base_member_after_dtor(int k) {
  D o(3 + k);
  o.~D();
  int r = o.x;
  new (&o) D(1);
  return r;
}
int x_derived_reuse(int k) {
  D o(3 + k);
  o.~D();
  new (&o) D(4 + k);
  return o.x + o.d;
}
// destroyed twice: the second destructor, at the end of the scope, only writes the object
int x_double_dtor_writes(int k) {
  S s(5 + k);
  s.~S();
  return 4 + k;
}
// destroyed twice: the second destructor reads the object
static int sum;
struct R {
  int x;
  R(int v) : x(v) {}
  ~R() { sum += x; }
};
int x_double_dtor_reads(int k) {
  {
    R r(5 + k);
    r.~R();
  }
  return sum;
}

// const objects: the destructor runs on them (const does not apply under destruction), and the end
// of their lifetime is no store by the program
int x_const_local(int k) {
  const S s(5 + k);
  return s.x;
}
int x_const_array(int k) {
  const S a[2] = {S(1 + k), S(2 + k)};
  return a[1].x;
}
static int use(const S &s) { return s.x; }
int x_static_const(int k) {
  static const S g(5);
  return use(g) + k;
}
int x_const_after_dtor(int k) {
  const S s(5 + k);
  s.~S();
  return s.x;
}

// the destructor variants: a virtual destructor called through a pointer to the base (D1 of the
// derived class through the vtable), delete through it (D0), virtual inheritance (D1 and the
// VTT-taking D2 of the bases)
struct V {
  int v = 1;
  virtual ~V() { v = -1; }
};
struct W : V {
  int w = 2;
  ~W() override { w = -2; }
};
int x_virtual_dtor_then_read(int k) {
  W o;
  V *p = &o;
  p->~V();
  int r = o.w;
  new (&o) W;
  return r + k;
}
int x_delete_through_base(int k) {
  V *p = new W;
  delete p;
  return 6 + k;
}
struct VA {
  int a = 1;
  virtual ~VA() {}
};
struct VB : virtual VA {
  int b = 2;
  ~VB() { b = -2; }
};
struct VC : virtual VA {
  int c = 3;
  ~VC() { c = -3; }
};
struct VD : VB, VC {
  int d = 4;
  ~VD() { d = -4; }
};
int x_vbase_dtor_then_read(int k) {
  VD o;
  o.~VD();
  int r = o.c;
  new (&o) VD;
  return r + k;
}
int x_vbase_reuse(int k) {
  VD o;
  o.~VD();
  new (&o) VD;
  return o.a + o.b + o.c + o.d + k;
}

// rog's L2: the backing array of an assigned initializer_list dies at the end of the assignment's
// full expression ([dcl.init.list]p6, [class.temporary]p4); the initializing list's lives with it
int x_initlist_assigned(int k) {
  std::initializer_list<int> il = {1, 2, 3};
  il = {4 + k, 5, 6};
  return *il.begin();
}
int x_initlist_in_scope(int k) {
  std::initializer_list<int> il = {1, 2 + k, 3};
  return il.begin()[1];
}
