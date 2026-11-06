// Const class objects under construction and destruction (run with CASES=constlife_cases.txt):
// const semantics do not apply to an object under construction or destruction (C++ [class.ctor],
// [class.dtor]), so its constructor and destructor may write it, also through a member function.
// A const class object in C++ is a plain block (constobj's gap: no read-only block for it), and
// ClangIR marks a class global constant (a read-only block) only when it is constant-initialized
// and its destruction is trivial or constant, so that no constructor or destructor runs on it in
// the program; an explicit destructor call ends its lifetime in the read-only block too
// ([basic.life]p1, p7). Expected result, labelled per case in the cases file: MATCH (the gaps
// included), or UB from cirrun.
#include <new>

struct P {
  int *p;
  int v;
  P(int *q) : p(nullptr), v(0) {
    p = q;
    v = *q;
    v += 1;
  }
  ~P() {
    *p = v;
    p = nullptr;
    v = 0;
  }
};
static int sink;

int c_local(int k) {
  int a = 5 + k;
  {
    const P x(&a);
    sink = x.v;
  }
  return a * 10 + sink;
}
struct Q {
  int n;
  void set(int v) { n = v; }
  Q(int v) : n(0) {
    set(v);
    set(n + 1);
  }
  ~Q() { set(-1); }
};
int c_ctor_member_call(int k) {
  const Q q(5 + k);
  return q.n;
}
int c_array(int k) {
  int a = 1 + k, b = 2 + k;
  {
    const P xs[2] = {P(&a), P(&b)};
    sink = xs[0].v + xs[1].v;
  }
  return a + b + sink;
}
int c_const_ref_temp(int k) {
  int a = 3 + k;
  {
    const P &r = P(&a);
    sink = r.v;
  }
  return a + sink;
}
struct B {
  int b;
  B() : b(1) {}
  ~B() { b = 0; }
};
struct D : B {
  int d;
  D(int v) : d(v) { b = 2; }
  ~D() {
    d = 0;
    b = 3;
  }
};
int c_derived(int k) {
  const D o(5 + k);
  return o.b * 10 + o.d;
}
struct M {
  mutable int c;
  M() : c(0) {}
  ~M() { c = -1; }
  void bump() const { ++c; }
};
int c_mutable(int k) {
  const M m;
  m.bump();
  m.bump();
  return m.c + k;
}

// objects of static storage duration
static int gs;
int c_static_local(int k) {
  static const P s(&gs);
  return s.v + k;
}
int exit_static_local(int *out) {
  static const P s(out);
  return 0;
}
static int g1 = 7;
const P gP(&g1);
int c_global(int k) { return gP.v + g1 + k; }
static int *outp;
struct W {
  int v;
  constexpr W(int x) : v(x) {}
  ~W() {
    if (outp)
      *outp = v;
    v = 0;
  }
};
const W gW(42);
int c_global_constant_init(int k) { return gW.v + k; }
int exit_global_constant_init(int *out) {
  outp = out;
  return 0;
}
// constant-initialized with constant destruction: read-only
struct W3 {
  int v;
  constexpr W3(int x) : v(x) {}
  constexpr ~W3() {}
};
constexpr W3 w3(5);
static int readv(const W3 &w) { return w.v; }
int c_constexpr_read_after_dtor(int k) {
  w3.~W3();
  return readv(w3) + k;
}
struct W2 {
  int v;
  constexpr W2(int x) : v(x) {}
  constexpr ~W2() { v = 0; }
};
constexpr W2 w2(5);
int c_constexpr_dtor_writes(int k) {
  w2.~W2();
  return k + 1;
}

// a const local's storage reused after its destructor ([basic.life]p10: undefined)
int c_reuse_const(int k) {
  int a = 0;
  const P x(&a);
  x.~P();
  new (const_cast<P *>(&x)) P(&a);
  return x.v + k;
}
