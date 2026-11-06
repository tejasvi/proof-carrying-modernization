// Member function pointers and function addresses as integers (run with CASES=intptr_cases.txt, which also
// has the C cases of intptr.c). In the Itanium C++ ABI a member function pointer is a pair of integers: the
// function's address, or 1 plus the offset of a virtual function in the vtable, and the adjustment of
// `this` in bytes. Clang converts the address back to a function pointer, moves `this` as a `void *` and
// reads the vtable slot through the vptr as bytes: function addresses, `void *` arithmetic in bytes and
// vptrs moved by whole slots. Each case is labelled in the cases file.
#include <cstdint>

struct B {
  int x;
  int get() { return x * 2; }
  int add(int k) { return x + k; }
};

static int call(B &b, int (B::*fn)()) { return (b.*fn)(); }

int x_pmf_nonvirtual(int k) {
  B b;
  b.x = k + 4;
  int (B::*g)(int) = &B::add;
  return call(b, &B::get) + (b.*g)(100);
}

struct V {
  virtual int f0() { return 10; }
  virtual int f1() { return 20; }
  virtual ~V() {}
};
struct W : V {
  int f1() override { return 21; }
};
typedef int (V::*VMF)();
static VMF pick(int i) { return i ? &V::f1 : &V::f0; }

int x_pmf_virtual(int k) {
  W w;
  VMF a = pick(0), b = pick(k);
  return (a ? (w.*a)() : 0) + (b ? (w.*b)() : 0) * 100;
}

struct P {
  int a;
  virtual int foo() = 0;
  int bar() { return a; }
};
struct Q {
  int b;
  virtual int foo() = 0;
  int bar() { return b * 10; }
};
struct R : P, Q {
  int c;
  int foo() override { return c * 100; }
  int bar() { return c * 1000; }
};
template <class T> static int invoke(R &r, int (T::*fn)()) { return (r.*fn)(); }

// adjustments of `this` to the second base, and virtual calls through its vptr
int x_pmf_multiple(int k) {
  R r;
  r.a = k;
  r.b = 2;
  r.c = 3;
  return invoke(r, &P::foo) + invoke(r, &P::bar) + invoke(r, &Q::foo) + invoke(r, &Q::bar) +
         invoke(r, &R::foo) + invoke(r, &R::bar);
}

struct C {
  int x;
  int f() { return 1; }
  int g() { return 2; }
  virtual int h() { return 3; }
};
typedef int (C::*CMF)();

int x_pmf_compare(int k) {
  CMF a = &C::f, b = &C::f, c = &C::g, d = &C::h, n = nullptr;
  return (a == b) + (a != c) * 10 + (d == &C::h) * 100 + (!n) * 1000 + (n == nullptr) * 10000 + k * 0;
}

int x_pmf_null_call(int k) {
  B b;
  b.x = k;
  int (B::*n)() = nullptr;
  return (b.*n)();
}

static int triple(int v) { return 3 * v; }

int x_function_roundtrip(int k) {
  std::uintptr_t u = reinterpret_cast<std::uintptr_t>(&triple);
  int (*g)(int) = reinterpret_cast<int (*)(int)>(u);
  return g(k) + (g == &triple) * 100;
}

// A local of a frame that a throw left has ended; its address as an integer designates nothing.
static std::uintptr_t x_saved;

static void x_throw_out(int k) {
  int x = k + 4;
  x_saved = reinterpret_cast<std::uintptr_t>(&x);
  throw 1;
}

int x_throw_access(int k) {
  try {
    x_throw_out(k);
  } catch (int) {
  }
  return *reinterpret_cast<int *>(x_saved);
}
