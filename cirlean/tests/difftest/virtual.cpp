// Virtual dispatch: overriders, two-level hierarchies, virtual destructors,
// calls through base references and pointers.
struct Shape {
  virtual int area() const = 0;
  virtual int sides() const { return 0; }
  virtual ~Shape() {}
};
struct Rect : Shape {
  int w, h;
  Rect(int a, int b) : w(a), h(b) {}
  int area() const override { return w * h; }
  int sides() const override { return 4; }
};
struct Tri : Shape {
  int b, h;
  Tri(int x, int y) : b(x), h(y) {}
  int area() const override { return b * h / 2; }
  int sides() const override { return 3; }
};
struct Square : Rect {
  explicit Square(int s) : Rect(s, s) {}
  int sides() const override { return 40; }
};

static int describe(const Shape &s) { return s.area() * 10 + s.sides(); }

int t_virt_rect(int a, int b) { Rect r(a, b); return describe(r); }
int t_virt_tri(int a, int b) { Tri t(a, b); return describe(t); }
int t_virt_square(int a) { Square s(a); return describe(s); }
int t_virt_heap(int a) {
  Shape *p = new Rect(a, 2);
  int r = describe(*p);
  delete p;
  return r;
}
int t_virt_array(int n) {
  Rect r(n, 3);
  Tri t(n, 4);
  const Shape *ps[2] = {&r, &t};
  int s = 0;
  for (int i = 0; i < 2; ++i) s += ps[i]->area();
  return s;
}
