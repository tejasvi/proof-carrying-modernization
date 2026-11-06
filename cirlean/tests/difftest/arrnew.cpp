// Array new of classes with constructors (run with CASES=arrnew_cases.txt). For new T[n] with a constant n,
// CIR converts the pointer to the first element, which the first typed view of the heap storage gives, to
// T(*)[n], decays it again and constructs the elements in a loop. Expected result (labelled per case in the
// cases file): MATCH, or UB from cirrun on the g_ gap (an array cookie: the storage of a class with a
// non-trivial destructor starts with the element count, which the model does not lay out).
struct Ctor {
  int x;
  Ctor() : x(4) {}
};
struct Poly {
  int x;
  virtual int f() const { return 7; }
};
struct Derived : Poly {
  int y = 2;
  int f() const override { return 9; }
};
struct Two {
  int a;
  double d;
  Two() : a(1), d(2.5) {}
};
struct Dtor {
  int x;
  Dtor() : x(3) {}
  ~Dtor() { counter += x; }
  static int counter;
};
int Dtor::counter = 0;

int a_ctor(int k) {
  Ctor *a = new Ctor[3];
  int s = a[0].x + a[2].x;
  delete[] a;
  return s + k;
}
int a_ctor_runtime(int k) {
  int n = 4 + k;
  Ctor *a = new Ctor[n];
  int s = 0;
  for (int i = 0; i < n; ++i) s += a[i].x;
  delete[] a;
  return s;
}
int a_poly_value_init(int k) {
  Poly *a = new Poly[3]();
  int s = 0;
  for (int i = 0; i < 3; ++i) {
    const Poly &r = a[i];
    s += r.f() + a[i].x;
  }
  delete[] a;
  return s + k;
}
int a_poly_default(int k) {
  Poly *a = new Poly[2];
  const Poly &r = a[1];
  int s = r.f();
  delete[] a;
  return s + k;
}
int a_derived(int k) {
  Derived *a = new Derived[2];
  const Poly &r = a[1];
  int s = r.f() * 10 + a[1].y;
  delete[] a;
  return s + k;
}
int a_two(int k) {
  Two *a = new Two[2];
  int s = a[1].a * 10 + (int) (a[1].d * 2);
  delete[] a;
  return s + k;
}
int a_one(int k) {
  Ctor *a = new Ctor[1];
  int s = a[0].x;
  delete[] a;
  return s + k;
}
int a_list(int k) {
  Ctor *a = new Ctor[3]{};
  int s = a[1].x;
  delete[] a;
  return s + k;
}
// gap: an array cookie
int g_dtor(int k) {
  Dtor *a = new Dtor[3];
  int s = a[2].x;
  delete[] a;
  return s * 100 + Dtor::counter + k;
}
