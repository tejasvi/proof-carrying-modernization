// Program startup and exit: constructor functions (`constructor(p)`), the dynamic
// initialization of globals (in order, `init_priority`, guarded: inline variables, static data
// members of templates, static locals), `atexit`, the destructors of static objects and
// `destructor(p)` functions. The `exit_` cases report the value they leave in `*out` when the
// program has exited.
#include <cstdlib>

static int seq = 0;
__attribute__((constructor(101))) static void init_101() { seq = seq * 10 + 1; }
__attribute__((constructor(103))) static void init_103() { seq = seq * 10 + 3; }
__attribute__((constructor(102))) static void init_102() { seq = seq * 10 + 2; }
int t_ctor_prio(int k) { return seq * 10 + k; }

static int calls = 0;
static int f(int x) { calls = calls * 10 + x; return x * 7; }
int g1 = f(3);
struct S { int a; S(int x) : a(x + 1) { calls = calls * 10 + 4; } ~S() { calls = 0; } };
S s1(5);
int h1 = g1 + s1.a;
int t_dyn_init(int k) { return h1 * 1000 + calls + k; }

static int pseq = 0;
struct P { int v; P(int x) : v(x) { pseq = pseq * 10 + x; } };
P p2 __attribute__((init_priority(2000)))(2);
P p1 __attribute__((init_priority(1000)))(1);
P p3(3);
int t_init_priority(int k) { return pseq * 10 + k + p1.v - p2.v + p3.v; }

static const int tbl[4] = {10, 20, 30, 40};
static int base = 0;
__attribute__((constructor(110))) static void set_base() { base = tbl[2]; }
static int derived = base + 1;
int t_ctor_dep(int k) { return derived + k; }

static int twice(int x) { return 2 * x; }
template <class T> struct Reg { static int v; };
template <class T> int Reg<T>::v = twice(4);
inline int iv = twice(21);
int t_guarded(int k) { return iv * 100 + Reg<int>::v + Reg<long>::v + k; }

static int counter = 0;
static int next_id() { return ++counter; }
static int &instance() { static int id = next_id() * 100; return id; }
int t_local_static(int k) {
  int a = instance();
  instance() += k;
  return a * 1000 + instance() + counter;
}

struct T { int v; T(int x) : v(x) { if (x < 0) throw x; } };
static int tries = 0;
static int make(int x) {
  ++tries;
  static T t(x);
  return t.v;
}
int t_local_static_throw(int k) {
  int r = 0;
  try { r = make(-k); } catch (int e) { r = e * 100; }
  int a = make(k);
  int b = make(k + 1);
  return r + a * 10 + b + tries * 1000;
}

static void on_exit_noop() {}
int t_atexit(int k) { return atexit(on_exit_noop) * 10 + k; }

static int *xout = nullptr;
static int xseq = 0;
static void xnote(int d) { xseq = xseq * 10 + d; if (xout) *xout = xseq; }
struct D { int d; D(int x) : d(x) {} ~D() { xnote(d); } };
D d_a(1);
D d_b __attribute__((init_priority(500)))(2);
__attribute__((destructor(300))) static void fini_300() { xnote(5); }
__attribute__((destructor(200))) static void fini_200() { xnote(6); }
__attribute__((destructor)) static void fini_dflt() { xnote(4); }
static void at1() { xnote(3); }
static void at2() { xnote(7); }
int exit_order(int *out) {
  xout = out;
  atexit(at1);
  atexit(at2);
  return 0;
}
static int lseq = 0;
static int *lout = nullptr;
struct L { int d; L(int x) : d(x) {} ~L() { lseq = lseq * 10 + d; if (lout) *lout = lseq; } };
static void use_local(int x) { static L l(x); }
int exit_local_static(int *out) {
  lout = out;
  use_local(8);
  use_local(9);
  static L first(1);
  return 0;
}

static int aseq = 0;
static int *aout = nullptr;
struct A { int d; A(int x) : d(x) {} ~A() { aseq = aseq * 10 + d; if (aout) *aout = aseq; } };
A arr[3] = {A(1), A(2), A(3)};
int exit_static_array(int *out) {
  aout = out;
  return arr[0].d + arr[2].d;
}
