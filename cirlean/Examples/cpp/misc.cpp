// Assorted loop-free functions: division semantics, short-circuit logic,
// switch fall-through, references, classes with multiple inheritance.
int arith_mix(int a, int b) {
  int s = a * 3 - b;
  s = s + (a / 2) - (b % 5);
  if (a > b) s += 7; else s -= 7;
  return s;
}

int ternary_chain(int a) {
  return a < 0 ? -1 : a == 0 ? 0 : a < 10 ? 1 : 2;
}

int bool_logic(int a, int b) {
  bool x = a > 0 && b > 0;
  bool y = a < 0 || b < 0;
  bool z = !(a == b);
  return x * 4 + y * 2 + z;
}

int switch_fall(int x) {
  int r = 0;
  switch (x) {
    case 1: r += 1;
    case 2: r += 10; break;
    case 3:
    case 4: r += 100; break;
    case 7: r += 1000;
    default: r += 5;
  }
  return r;
}

static void bump(int &r, int k) { r += k; }
int refs(int a) {
  int x = a;
  int &r = x;
  bump(r, 5);
  bump(x, 1);
  return x;
}

struct Base {
  int v;
  Base(int x) : v(x) {}
  int get() const { return v; }
};
struct Mid : Base { int m; Mid(int x) : Base(x), m(x * 2) {} };
struct Derived : Mid {
  int d;
  Derived(int x) : Mid(x + 1), d(3) {}
  int sum() const { return get() + m + d; }
};
struct Other { int o; };
struct Multi : Other, Base { Multi(int x) : Base(x) { o = 9; } };

int inherit(int x) {
  Derived d(x);
  Multi m(x);
  const Base &b = m;
  return d.sum() * 100 + b.get() + m.o;
}
