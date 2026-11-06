// Virtual inheritance (run with CASES=vbase_cases.txt): the VTT (`cir.vtt.address_point`, both
// forms) from which the base-object constructors and destructors of a class with virtual bases
// set the vptrs, construction vtables (the virtual calls of a base's constructor and destructor
// see the base's overriders), virtual base offsets read from the vtable (vptr - 24) for member
// access through a pointer to a derived class, virtual thunks, and the vptr of a virtual base set
// through a pointer of the derived class's type; also non-virtual thunks (a virtual call through
// a non-primary base of a class without virtual bases). Expected result (labelled per case in the
// cases file): MATCH on every case.

struct V {
  int v;
  explicit V(int x) : v(x) {}
  virtual int who() const { return 1; }
  virtual int vget() const { return v; }
  virtual ~V() {}
};

struct A : virtual V {
  int a, seenA, seenAV;
  int *log;
  A(int x, int *lg) : V(x), a(x + 1), log(lg) {
    seenA = who();                          // A::who (construction vtable)
    seenAV = static_cast<V *>(this)->who(); // through the virtual base: still A::who
  }
  int who() const override { return 2; }
  ~A() override { if (log) *log = *log * 10 + who(); }
};

struct B : virtual V {
  int b, seenB;
  int *log;
  B(int x, int *lg) : V(x), b(x + 2), log(lg) { seenB = who(); } // V::who (B has none)
  ~B() override { if (log) *log = *log * 10 + who(); }
};

struct D : A, B {
  int d;
  D(int x, int *lg) : V(x * 10), A(x, lg), B(x, lg), d(x + 3) {}
  int who() const override { return 4; }
  ~D() override { if (A::log) *A::log = *A::log * 10 + who(); }
};

struct F : D {
  int f;
  F(int x, int *lg) : V(x * 100), D(x, lg), f(x + 5) {}
  int who() const override { return 6; }
};

struct E : virtual V {
  E(int x) : V(x) {}
};

static int readV(const A *p) { return p->v; }
static int readVB(const B *p) { return p->v; }
static int viaV(const V &r) { return r.who() * 100 + r.vget(); }

// the diamond: one V, members of every class
int t_diamond(int x) {
  D d(x, nullptr);
  return d.v + d.a + d.b + d.d;
}

// member of the virtual base through pointers to the two bases (vbase offsets from two vtables)
int t_vbase_member(int x) {
  D d(x, nullptr);
  return readV(&d) * 1000 + readVB(&d);
}

// a write through one base seen through the other
int t_vbase_write(int x) {
  D d(x, nullptr);
  B *pb = &d;
  pb->v = x + 7;
  return readV(&d);
}

// the base constructors' virtual calls see the bases' overriders (construction vtables)
int t_ctor_calls(int x) {
  D d(x, nullptr);
  return d.seenA * 100 + d.seenAV * 10 + d.seenB + x * 0;
}

// a virtual call through the virtual base (virtual thunk to D::who) and its data member
int t_thunk_call(int x) {
  D d(x, nullptr);
  return viaV(d);
}

// destructors: each sees its own class's overrider, in reverse order of construction
int t_dtor_calls(int x) {
  int log = x;
  { D d(x, &log); }
  return log;
}

// a further derived class: D's base-object constructor gets its part of F's VTT
int t_further(int x) {
  F f(x, nullptr);
  return viaV(f) * 10 + f.seenA + readV(&f) + readVB(&f) + f.f;
}

// destructors of the further derived object
int t_further_dtor(int x) {
  int log = 0;
  { F f(x, &log); }
  return log;
}

// new, a virtual call and delete through the virtual base (the deleting destructor's thunk)
int t_heap(int x) {
  int log = 0;
  V *p = new D(x, &log);
  int r = p->who() * 1000 + p->vget();
  delete p;
  return r * 100 + log;
}

// a lone virtual base
int t_single(int x) {
  E e(x);
  return viaV(e);
}

struct P {
  int pv = 5;
  virtual int p() const { return 1; }
  virtual ~P() {}
};

struct Q {
  int qv = 7;
  virtual int q() const { return 2; }
  virtual ~Q() {}
};

struct PQ : P, Q {
  int *log = nullptr;
  int q() const override { return 20 + qv; }
  ~PQ() override { if (log) *log = 9; }
};

// a virtual call through a non-primary base (a non-virtual thunk to PQ::q)
int t_nonprimary(int x) {
  PQ o;
  Q &r = o;
  return r.q() * 10 + x;
}

// delete through a non-primary base (the deleting destructor's non-virtual thunk)
int t_nonprimary_delete(int x) {
  int log = 0;
  PQ *o = new PQ;
  o->log = &log;
  Q *r = o;
  int v = r->q();
  delete r;
  return v * 100 + log * 10 + x;
}
