// Function aliases (CASES=alias_cases.txt). Clang emits the complete-object constructor and destructor
// (C1, D1) of a class without virtual bases, defined out of line, as aliases of the base-object ones
// (C2, D2), in the vtable too; __attribute__((alias)) gives a function another name, also an alias of
// an alias. Before the change, a call of an alias was UB ("call to an external function without a
// model").
#include <cstdarg>

// --- constructors: C1 is an alias of C2
struct Point {
  int x, y;
  Point(int a, int b);
};
Point::Point(int a, int b) : x(a), y(b * 2) {}
int t_ctor_alias(int k) {
  Point p(k, 3);
  return p.x * 100 + p.y;
}

// through new, and for the elements of an array
int t_ctor_alias_new(int k) {
  Point *p = new Point(k, k + 1);
  Point arr[2] = {Point(1, 2), Point(k, 0)};
  int r = p->x * 1000 + p->y * 100 + arr[0].y * 10 + arr[1].x;
  delete p;
  return r;
}

// --- destructors: D1 is an alias of D2
static int destroyed = 0;
struct Tracker {
  int id;
  Tracker(int i);
  ~Tracker();
};
Tracker::Tracker(int i) : id(i) {}
Tracker::~Tracker() { destroyed = destroyed * 10 + id; }
int t_dtor_alias(int k) {
  destroyed = 0;
  {
    Tracker a(1);
    Tracker b(k);
  }
  return destroyed;
}

// a virtual destructor: delete through the base runs the deleting destructor (D0), which calls the
// D1 alias; an explicit destructor call goes through the vtable's D1 entry, an alias
struct Base {
  int b;
  Base();
  virtual ~Base();
};
Base::Base() : b(5) {}
Base::~Base() { destroyed += 100; }
struct Derived : Base {
  int d;
  Derived(int v);
  ~Derived() override;
};
Derived::Derived(int v) : d(v) {}
Derived::~Derived() { destroyed += d; }
int t_virtual_dtor_alias(int k) {
  destroyed = 0;
  Base *p = new Derived(k);
  int r = p->b;
  delete p;
  return destroyed * 10 + r;
}
int t_virtual_dtor_call(int k) {
  destroyed = 0;
  Base *p = new Derived(k);
  p->~Base();
  // the storage is not freed (a leak, which is not undefined)
  return destroyed;
}

// --- __attribute__((alias)): another name of a function, and an alias of that alias
extern "C" int add_one(int x) { return x + 1; }
extern "C" int inc(int) __attribute__((alias("add_one")));
extern "C" int inc2(int) __attribute__((alias("inc")));
int t_c_alias(int k) { return inc(k) * 100 + inc2(k + 1); }

// the same function: the addresses compare equal (C11 6.5.9p6)
int t_c_alias_addr(int k) {
  int (*f)(int) = inc;
  int (*g)(int) = add_one;
  int (*h)(int) = inc2;
  return (f == g) * 100 + (h == g) * 10 + f(k) - g(k);
}

// in a table of function pointers (a global initializer)
static int (*const table[3])(int) = {add_one, inc, inc2};
int t_c_alias_table(int k) { return table[0](k) + table[1](k) * 10 + table[2](k) * 100 + (table[0] == table[2]); }

// an alias of a function with internal linkage (named by its mangled name), which the program also
// calls directly
static int thrice_impl(int x) { return 3 * x; }
extern "C" int thrice(int) __attribute__((alias("_ZL11thrice_impli")));
int t_c_alias_static(int k) { return thrice(k) * 100 + thrice_impl(k + 1); }

// gap (ClangIR's): a static function that only an alias uses is not emitted, so the alias has no body
// and its call is UB
static int twice_impl(int x) { return 2 * x; }
extern "C" int twice(int) __attribute__((alias("_ZL10twice_impli")));
int t_gap_c_alias_static_unused(int k) { return twice(k); }

// a variadic function through an alias: the arguments after the parameters keep their types
extern "C" int sum_impl(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int s = 0;
  for (int i = 0; i < n; ++i) s += va_arg(ap, int);
  va_end(ap);
  return s;
}
extern "C" int sum(int n, ...) __attribute__((alias("sum_impl")));
int t_c_alias_varargs(int k) { return sum(3, k, 10, 100); }

// UB: va_arg(ap, int) of a long that the call through the alias passed (C11 7.16.1.1p2)
int t_ub_c_alias_varargs_long(int k) { return sum(1, (long)k); }

// UB: signed overflow in the alias's target (C11 6.5p5): the alias runs the target's body
int t_ub_c_alias_overflow(int k) { return inc(2147483647 - 4 + k); }
