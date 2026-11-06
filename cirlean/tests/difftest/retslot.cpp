// Results of class types that are non-trivial for calls (run with CASES=retslot_cases.txt).
// Such a result is one object: the caller's, which the callee's return statement initializes
// directly (C++ [dcl.init.general]p16.6.1, [stmt.return]p2, [class.temporary]p3; the Itanium ABI
// passes its address). Expected result (labelled per case in the cases file): MATCH; the trivially
// copyable control keeps the value copy.
#include <map>
#include <set>
#include <string>

// a class that points at itself: a copy points at the copy
struct SelfRef {
  SelfRef *self;
  int v;
  explicit SelfRef(int x) : self(this), v(x) {}
  SelfRef(const SelfRef &o) : self(this), v(o.v) {}
  ~SelfRef() {}
};
// a prvalue result: no copy (guaranteed elision)
static SelfRef make_self(int x) { return SelfRef(x); }
int r_self_addr(int k) {
  SelfRef s = make_self(3 + k);
  return (s.self == &s) * 10 + s.v;
}
// a named result (the named return value)
static SelfRef make_named(int x) {
  SelfRef t(x);
  t.v += 1;
  return t;
}
int r_named(int k) {
  SelfRef s = make_named(5 + k);
  return (s.self == &s) * 10 + s.v;
}
// two named objects, so no named return value: the copy constructor builds the result
static SelfRef pick(int x) {
  SelfRef a(x), b(x + 100);
  if (x > 0) return a;
  return b;
}
int r_two_returns(int k) {
  SelfRef s = pick(k);
  return (s.self == &s) * 1000 + s.v;
}
// a result returned on through a second function
static SelfRef pass_on(int x) { return make_self(x + 1); }
int r_chain(int k) {
  SelfRef s = pass_on(k);
  return (s.self == &s) * 10 + s.v;
}
// a result that initializes a member
struct Holder {
  SelfRef s;
  explicit Holder(int x) : s(make_self(x)) {}
};
int r_member(int k) {
  Holder h(4 + k);
  return (h.s.self == &h.s) * 10 + h.s.v;
}
// a by-value parameter returned: the copy constructor builds the result from it
static SelfRef ident(SelfRef p) { return p; }
int r_param(int k) {
  SelfRef a(6 + k);
  SelfRef b = ident(a);
  return (b.self == &b) * 10 + b.v;
}
// a virtual function returning one (an indirect call)
struct Base {
  virtual SelfRef get(int x) const { return SelfRef(x); }
  virtual ~Base() {}
};
struct Derived : Base {
  SelfRef get(int x) const override { return SelfRef(2 * x); }
};
int r_virtual(int k) {
  Derived d;
  const Base &b = d;
  SelfRef s = b.get(3 + k);
  return (s.self == &s) * 100 + s.v;
}
// a class that registers its address
static const void *registered = nullptr;
struct Reg {
  int v;
  explicit Reg(int x) : v(x) { registered = this; }
  Reg(const Reg &o) : v(o.v) { registered = this; }
  ~Reg() {
    if (registered == this) registered = nullptr;
  }
};
static Reg make_reg(int x) { return Reg(x); }
int r_registered(int k) {
  Reg r = make_reg(1 + k);
  return (registered == &r) * 10 + r.v;
}
// a discarded result: a temporary, destroyed at the end of the full expression
static int dtors = 0;
struct Counted {
  int v;
  explicit Counted(int x) : v(x) {}
  Counted(const Counted &o) : v(o.v) {}
  ~Counted() { ++dtors; }
};
static Counted make_counted(int x) { return Counted(x); }
int r_discard(int k) {
  dtors = 0;
  make_counted(k);
  return dtors;
}
// the results of a conditional expression
int r_conditional(int k) {
  SelfRef s = k > 0 ? make_self(10) : make_self(20);
  return (s.self == &s) * 100 + s.v;
}
// std::map and std::set (libc++: the end node is a member of the tree) returned by value
static std::map<int, int> make_map(int k) {
  std::map<int, int> m;
  m[1] = 10 + k;
  m[2] = 20;
  return m;
}
int r_map(int k) {
  std::map<int, int> m = make_map(k);
  int s = 0;
  for (const auto &e : m) s += e.second;
  return s * 10 + (int)m.size();
}
static std::set<int> make_set(int k) {
  std::set<int> s = {3, 1, 2 + k};
  return s;
}
int r_set(int k) {
  std::set<int> s = make_set(k);
  int first = *s.begin(), n = (int)s.size();
  return first * 10 + n;
}
// a std::string returned by value
static std::string make_string(int n) { return std::string(n, 'x'); }
int r_string(int k) {
  std::string s = make_string(3 + k);
  return (int)s.size();
}
// control: a trivially copyable struct keeps the value copy
struct TP {
  int a, b;
};
static TP make_tp(int x) { return TP{x, x + 1}; }
int c_trivial_ret(int k) {
  TP t = make_tp(k + 2);
  return t.a * 10 + t.b;
}
// gap (the evidence-owner session's probe, checks/byval-20261029T025320Z/probe/ret.cpp): a class pointing into itself whose user copy
// constructor the named return value elides and which has no destructor; the module emits neither, so the frontend
// cannot tell it is non-trivial for calls, the result is copied out of the callee's slot, and the caller's copy
// points into the dead slot (CHANGES_retslot.md, Limits)
struct Elided {
  char buf[8];
  char *p;
  Elided() : p(buf) { buf[0] = 'a'; }
  Elided(const Elided &o) : p(buf) { buf[0] = o.buf[0]; }
};
static Elided make_elided() {
  Elided e;
  e.buf[0] = 'x';
  return e;
}
int g_elided_copy(int k) {
  Elided e = make_elided();
  e.buf[0] = 'y';
  return (*e.p == 'y') ? 1 + k : -1;
}
