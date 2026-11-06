// Classes, references, arrays, pointers, inheritance.
struct Point {
  int x, y;
  Point(int a, int b) : x(a), y(b) {}
  int dot(const Point &o) const { return x * o.x + y * o.y; }
  void scale(int k) { x *= k; y *= k; }
};

int t_point(int a, int b) {
  Point p(a, b), q(b, a);
  p.scale(2);
  return p.dot(q) + q.x;
}

static void bump(int &r, int k) { r += k; }
int t_refs(int a) {
  int x = a;
  int &r = x;
  bump(r, 5);
  bump(x, 1);
  return x;
}

int t_array_sum(int n) {
  int arr[8];
  for (int i = 0; i < 8; ++i) arr[i] = i * n;
  int s = 0;
  for (int *p = arr; p != arr + 8; ++p) s += *p;
  return s + (int)(&arr[5] - &arr[1]);
}

struct Pair { int a; int b; };
int t_struct_array(int n) {
  Pair ps[4];
  for (int i = 0; i < 4; ++i) { ps[i].a = i; ps[i].b = n - i; }
  int s = 0;
  for (const Pair &p : ps) s += p.a * p.b;
  return s;
}

struct Base {
  int v;
  Base(int x) : v(x) {}
  int get() const { return v; }
};
struct Mid : Base { int m; Mid(int x) : Base(x), m(x * 2) {} };
struct Derived : Mid { int d; Derived(int x) : Mid(x + 1), d(3) {} int sum() const { return get() + m + d; } };
struct Other { int o; };
struct Multi : Other, Base { Multi(int x) : Base(x) { o = 9; } };

int t_inherit(int x) {
  Derived d(x);
  Multi m(x);
  const Base &b = m;
  return d.sum() * 100 + b.get() + m.o;
}

int t_swap_ptrs(int a, int b) {
  int x = a, y = b;
  int *p = &x, *q = &y;
  int t = *p; *p = *q; *q = t;
  return x * 1000 + y;
}

int t_2d_array(int n) {
  int g[3][4];
  for (int i = 0; i < 3; ++i)
    for (int j = 0; j < 4; ++j) g[i][j] = i * n + j;
  return g[2][3] + g[1][1] * 10;
}
