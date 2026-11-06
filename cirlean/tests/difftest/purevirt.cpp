// __cxa_pure_virtual (run with CASES=purevirt_cases.txt): the vtable slot of a
// pure virtual function. Classes with pure virtual functions work through
// their overrides; a call of the pure virtual function itself (from the base
// class's constructor, while the object is still a Base) is undefined. Expected
// result (labelled per case in the cases file): MATCH on the t_* cases; UB
// "pure virtual call" on u_pure_call (natively the C++ runtime aborts).

struct Shape {
  virtual int area() const = 0;
  virtual ~Shape() {}
  int twice() const { return 2 * area(); }
};

struct Square : Shape {
  int s;
  explicit Square(int s) : s(s) {}
  int area() const override { return s * s; }
};

struct Base {
  Base() { init(); }
  void init() { f(); }
  virtual int f() = 0;
  virtual ~Base() {}
};

struct Derived : Base {
  int f() override { return 1; }
};

int t_pure_override(int n) {
  Square q(n);
  const Shape &s = q;
  return s.twice();
}

int t_pure_heap(int n) {
  Shape *p = new Square(n);
  int a = p->area();
  delete p;
  return a + 1;
}

int u_pure_call(int n) {
  Derived d;
  return n + d.f();
}
