// Further features, and known gaps (expected UB: unsupported).
#include <vector>
#include <string>

int g_counter = 5;
const int g_table[4] = {2, 3, 5, 7};
int t_globals(int n) {
  g_counter += n;
  return g_counter * 10 + g_table[n % 4];
}

struct Tok {
  int *acc; bool ok;
  Tok(int *a, bool o) : acc(a), ok(o) {}
  ~Tok() { ++*acc; }
  explicit operator bool() const { return ok; }
};
int t_cond_var(int n) {
  int acc = 0, i = 0;
  while (Tok t{&acc, i < n}) { ++i; }
  return acc * 100 + i;
}

struct Big { int a[3]; int b; };
static Big make_big(int x) { Big r; for (int i = 0; i < 3; ++i) r.a[i] = x + i; r.b = -x; return r; }
int t_struct_copy(int x) {
  Big p = make_big(x);
  Big q = p;
  q.a[1] = 100;
  return p.a[1] * 1000 + q.a[1] + q.b;
}

static int twice(int v) { return 2 * v; }
static int inc(int v) { return v + 1; }
int t_fnptr(int x) {
  int (*f)(int) = x > 0 ? twice : inc;
  int (*g)(int) = inc;
  return f(x) * 100 + g(f(1));
}

int t_do_continue(int n) {
  int i = 0, s = 0;
  do {
    ++i;
    if (i % 2) continue;
    s += i;
  } while (i < n);
  return s;
}

int t_str_default(int n) {
  std::string s;
  for (int i = 0; i < n; ++i) s.push_back('a' + i);
  s += "!";
  return (int)s.size() * 100 + s[n - 1];
}

// ---- known gaps ----
int t_gap_emplace(int n) {      // emplace_back returns T& (closed: modelled since contb)
  std::vector<int> v;
  v.emplace_back(n);
  return v[0];
}

int t_gap_iter_lt(int n) {      // C++20 `<` on iterators goes through operator<=>
  std::vector<int> v{1, 2, 3};
  return (v.begin() < v.end()) * 10 + n;
}

struct Bits { unsigned a : 3; unsigned b : 5; };
int t_gap_bitfield(int n) {     // cir.get_bitfield / cir.set_bitfield
  Bits x; x.a = n; x.b = n + 1;
  return x.a * 100 + x.b;
}

struct Shape { virtual int area() const { return 1; } virtual ~Shape() {} };
struct Sq : Shape { int s; Sq(int x) : s(x) {} int area() const override { return s * s; } };
int t_gap_virtual(int n) {      // vtables: cir.vtable.*
  Sq q(n);
  const Shape &r = q;
  return r.area();
}

int t_gap_goto(int n) {         // cir.goto / cir.label
  int i = 0;
again:
  ++i;
  if (i < n) goto again;
  return i;
}

union U2 { int i; short s[2]; };
struct R2 { unsigned char type; union { unsigned char ch; unsigned char *ccl; } u; };
static R2 table2[4];
int t_union(int x) {        // one active member at a time
  U2 u;
  u.i = x;
  int a = u.i;
  u.s[0] = 3;
  return a * 10 + u.s[0];
}
int t_static_union(int k) {  // static storage is zero-initialised, unions too
  int r = table2[k].type + table2[k].u.ch;
  table2[k].u.ch = 7;
  return r * 100 + table2[k].u.ch;
}

static char *const marks[3] = {(char *)1, (char *)0, (char *)7};
int t_int_ptr(int k) {  // integer-valued pointers: compared and cast back only
  char *p = marks[k];
  return (p == (char *)1 ? 100 : 0) + (p == 0 ? 10 : 0) + (int)(long)p;
}
