// rog's audit item M14 (run with MODE=status CASES=audit2exit_cases.txt): the destructor of an object
// of static storage duration ends its lifetime ([basic.start.term]p1, [basic.life]p1.4), so a
// handler or a destructor that runs after it and uses the object has undefined behaviour
// ([basic.life]p7): an atexit handler registered before the object's construction runs after its
// destructor ([basic.start.term]p3), and objects are destroyed in the reverse order of their
// construction. The test functions return or _Exit with a status; expected result, labelled per case
// in the cases file: MATCH, or UB from cirrun.
#include <cstdlib>

struct G {
  int v;
  G(int x) : v(x) {}
  ~G() { v = 9; }
};
static G *gp;
static void h_read() { std::_Exit(gp->v); }
static void h_write() {
  gp->v = 4;
  std::_Exit(3);
}

// a handler registered before the object's construction reads it after its destructor
int e_handler_reads_destroyed(int k) {
  std::atexit(h_read);
  static G g(5 + k);
  gp = &g;
  return 0;
}
// control: the object constructed before the registration is destroyed after the handler
int e_handler_reads_live(int k) {
  static G g(5 + k);
  gp = &g;
  std::atexit(h_read);
  return 0;
}
// a handler registered before the object's construction writes it after its destructor
int e_handler_writes_destroyed(int k) {
  std::atexit(h_write);
  static G g(6 + k);
  gp = &g;
  return 0;
}

// a static object's destructor reads another one, constructed after it, so destroyed before it
struct R {
  G *other;
  R() : other(nullptr) {}
  ~R() {
    if (other) std::_Exit(other->v);
  }
};
int e_dtor_reads_destroyed(int k) {
  static R r;
  static G g(7 + k);
  r.other = &g;
  return 0;
}
// control: the object read was constructed before, so it is destroyed after the reader
int e_dtor_reads_live(int k) {
  static G g(8 + k);
  static R r;
  r.other = &g;
  return 0;
}

// a namespace-scope object with a destructor, constructed before main; a handler registered in the
// test function runs before its destructor
static G global_g(11);
static void h_read_global() { std::_Exit(global_g.v); }
int e_handler_reads_global(int k) {
  std::atexit(h_read_global);
  return k;
}
