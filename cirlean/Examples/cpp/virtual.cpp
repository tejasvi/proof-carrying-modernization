// Virtual dispatch through a base-class reference.
struct Shape {
  virtual int area() const = 0;
  virtual ~Shape() {}
};

struct Rect : Shape {
  int w, h;
  Rect(int a, int b) : w(a), h(b) {}
  int area() const override { return w * h; }
};

struct Square : Rect {
  explicit Square(int s) : Rect(s, s) {}
};

int area_of(const Shape &s) { return s.area(); }

int rect_area(int w, int h) {
  Rect r(w, h);
  return area_of(r);
}

int square_area(int s) {
  Square q(s);
  return area_of(q);
}
