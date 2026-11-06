// By-value parameters of class types that are non-trivial for calls (run with CASES=byval_cases.txt).
// Such a parameter is one object: the caller's temporary, initialized by the copy or move
// constructor, which the callee uses in place and the caller destroys at the end of the full
// expression (C++ [expr.call]p7, [class.temporary]p3; the Itanium ABI passes it by address).
// Expected result (labelled per case in the cases file): MATCH; the trivially copyable control
// keeps the value copy.
#include <list>
#include <memory>
#include <utility>
#include <vector>

// math_fibonacci_sum's shape: a matrix (a vector of vectors, no model) by value, moved from by the
// callee's return, recursing as t = power(t, n / 2)
using matrix = std::vector<std::vector<long>>;
static matrix mul(const matrix &a, const matrix &b) {
  matrix r(2, std::vector<long>(2, 0));
  for (int i = 0; i < 2; ++i)
    for (int j = 0; j < 2; ++j)
      for (int k = 0; k < 2; ++k) r[i][j] += a[i][k] * b[k][j];
  return r;
}
static matrix power(matrix t, int ex) {
  matrix a = {{1, 1}, {1, 0}};
  if (ex == 0 || ex == 1) return t;
  t = power(t, ex / 2);
  t = mul(t, t);
  if (ex & 1) t = mul(t, a);
  return t;
}
int b_power(int k) {
  matrix f = {{1, 1}, {1, 0}};
  matrix r = power(f, 4 + k);
  return (int)(r[0][1] * 10 + f[0][0]);
}

// a std::unique_ptr by value: used in place, and moved on by the callee
static int consume(std::unique_ptr<int> p) { return *p + 1; }
int b_unique_ptr(int k) {
  std::unique_ptr<int> p(new int(41 + k));
  int r = consume(std::move(p));
  return r * 10 + (p == nullptr);
}
static std::unique_ptr<int> pass(std::unique_ptr<int> p) { return p; }
int b_unique_ptr_move(int k) {
  std::unique_ptr<int> q = pass(std::make_unique<int>(7 + k));
  return *q;
}

// a user RAII class: counts its live objects and its constructions; each parameter is constructed
// once, by the caller, and destroyed once, by the caller
static int live = 0, made = 0;
struct Res {
  int *p;
  explicit Res(int v) : p(new int(v)) { ++live; ++made; }
  Res(const Res &o) : p(new int(*o.p)) { ++live; ++made; }
  Res(Res &&o) noexcept : p(o.p) { o.p = nullptr; ++live; ++made; }
  ~Res() { delete p; --live; }
};
static int use(Res r) { return *r.p + live * 100; }
int b_raii_copy(int k) {
  live = 0;
  made = 0;
  int v;
  {
    Res a(5 + k);
    v = use(a);
  }
  return v * 100 + live * 10 + made;
}
static Res keep(Res r) {
  *r.p += 1;
  return r;
}
int b_raii_move(int k) {
  live = 0;
  made = 0;
  int v;
  {
    Res a = keep(Res(3 + k));
    v = *a.p;
  }
  return v * 100 + live * 10 + made;
}

// a std::list (no model; libc++'s nodes owned through pointers, the end node inside the list
// object) by value
static int lsum(std::list<int> l) {
  l.reverse();
  l.push_back(9);
  return l.front() * 100 + l.back() * 10 + (int)l.size();
}
int b_list(int k) {
  std::list<int> a = {1, 2, 3 + k};
  int s = lsum(a);
  return s * 10 + a.front();
}
// strand_sort's shape, the std::list also returned by value: the callee builds the result in the
// caller's object (retslot.cpp), so its nodes point at that object's end node
static std::list<int> rev(std::list<int> l) {
  l.reverse();
  return l;
}
int g_list_return(int k) {
  std::list<int> a = {1, 2, 3 + k};
  std::list<int> b = rev(a);
  return b.front() * 100 + a.front() * 10 + (int)b.size();
}

// control: a trivially copyable struct by value keeps the value copy; the caller's object does not
// change
struct P {
  int x, y;
};
static int sum(P p) {
  p.x += 10;
  return p.x + p.y;
}
int c_trivial(int k) {
  P a = {1 + k, 2};
  int s = sum(a);
  return s * 10 + a.x;
}

// the thrift pattern: a std::shared_ptr passed by value to a callee that moves from it, into a
// member or a local; the caller then checks use_count() or uses the object (gaps: the release of the
// last owner calls libc++'s __shared_weak_count::__release_weak(), which has no model; make_shared
// constructs into storage, type-punned access, so the cases use shared_ptr(new T))
struct Transport {
  int v;
};
struct Protocol {
  std::shared_ptr<Transport> t;
  explicit Protocol(std::shared_ptr<Transport> tr) : t(std::move(tr)) {}
};
static Protocol *kept = nullptr;
// into a member of an object that outlives the call (it stays allocated)
int b_shared_member_count(int k) {
  std::shared_ptr<Transport> tr(new Transport{40 + k});
  kept = new Protocol(tr);
  return (int)tr.use_count() * 100 + kept->t->v;
}
// the same with both owners left allocated, so no use count reaches 0 on the path
int b_shared_leaked_count(int k) {
  std::shared_ptr<Transport> *tr = new std::shared_ptr<Transport>(new Transport{40 + k});
  kept = new Protocol(*tr);
  return (int)tr->use_count() * 100 + (*tr)->v;
}
// into a member of a local object, destroyed at the end of its block
int b_shared_member_scope(int k) {
  std::shared_ptr<Transport> tr(new Transport{40 + k});
  int c;
  {
    Protocol p(tr);
    c = (int)tr.use_count();
  }
  return c * 100 + (int)tr.use_count() * 10 + tr->v;
}
// into a local of the callee
static int sink(std::shared_ptr<Transport> s) {
  std::shared_ptr<Transport> local = std::move(s);
  return local->v + (int)local.use_count() * 100;
}
int b_shared_local(int k) {
  std::shared_ptr<Transport> tr(new Transport{7 + k});
  int r = sink(tr);
  return r * 100 + (int)tr.use_count() * 10 + tr->v;
}
