// std::vector objects that hold libc++'s members of an empty vector without a constructor call of
// the model (a static local, a class with a defaulted constructor; the constant-initialized globals
// are in vecfixg.cpp) and vector(first, last), which libc++ spells with an enable_if;
// std::vector<bool> and its reference proxy; value-initialization of a polymorphic object, which
// zeroes the object, its vptr too, before the constructor stores the vptr (run with
// CASES=vecfix_cases.txt). Expected result (labelled per case in the cases file): MATCH, or UB from
// cirrun on the u_ cases and on the g_ gaps (defined in C++, not modelled). Native runs print what
// libstdc++'s code gives on the u_ cases.
#include <cstddef>
#include <cstring>
#include <stdexcept>
#include <utility>
#include <vector>

// vectors without a constructor call of the model (constant-initialized globals: vecfixg.cpp)
int e_static_local(int k) {
  static std::vector<int> v;
  v.push_back(k + 2);
  v.push_back(k + 3);
  return (int)v.size() * 10 + v[1];
}
struct Defaulted {
  std::vector<int> v;
  Defaulted() = default;
};
int e_defaulted_ctor(int k) {
  Defaulted d;
  d.v.push_back(k + 1);
  return (int)d.v.size() * 10 + d.v[0];
}
int e_defaulted_new(int k) {
  Defaulted *d = new Defaulted();
  d->v.push_back(k + 2);
  int r = (int)d->v.size() * 10 + d->v[0];
  delete d;
  return r;
}

// vector(first, last)
int r_range_ptr(int k) {
  int a[] = {3, 1, 4, 1, 5};
  std::vector<int> v(a + 1, a + 4);
  return (int)v.size() * 100 + v[0] * 10 + v[2] + k;
}
int r_range_const_ptr(int k) {
  const int a[] = {2, 7, 1, 8};
  std::vector<int> v(a, a + 4);
  return v[1] * 10 + v[3] + k;
}
int r_range_iter(int k) {
  std::vector<int> w = {9, 8, 7, 6};
  std::vector<int> v(w.begin() + 1, w.end());
  v[0] += k;
  return (int)v.size() * 100 + v[0] * 10 + w[1] - 8;
}
int r_range_empty(int k) {
  int a[] = {1, 2};
  std::vector<int> v(a, a);
  return (int)v.size() * 10 + (int)v.empty() + k;
}
int r_range_alloc(int k) {
  long a[] = {10, 20, 30};
  std::vector<long> v(a, a + 3, std::allocator<long>());
  return (int)(v[0] + v[2]) + k;
}
int r_range_double(int k) {
  double a[] = {0.5, 1.25, 2.0};
  std::vector<double> v(a, a + 3);
  return (int)((v[0] + v[1] + v[2]) * 4) + k;
}
// undefined: the end of the range before its start
int u_range_reversed(int k) {
  int a[] = {1, 2, 3};
  std::vector<int> v(a + 2, a);
  return (int)v.size() + k;
}

// std::vector<bool>
static int count_true(const std::vector<bool> &v) {
  int c = 0;
  for (std::size_t i = 0; i < v.size(); ++i) c += v[i];
  return c;
}
int b_fill_index(int k) {
  std::vector<bool> v(5, false);
  v[2] = true;
  v[4] = k > 0;
  return (int)v.size() * 100 + v[2] * 10 + v[1] + v[4] * 2;
}
int b_size_ctor(int k) {
  std::vector<bool> v(4);
  return (int)v.size() * 10 + v[3] + k;
}
int b_init_list(int k) {
  std::vector<bool> v{true, false, true, true};
  return count_true(v) * 10 + v[1] + k;
}
int b_default_empty(int k) {
  std::vector<bool> v;
  return (int)v.empty() * 10 + (int)v.size() + k;
}
int b_push_pop(int k) {
  std::vector<bool> v;
  for (int i = 0; i < 70 + k; ++i) v.push_back(i % 3 == 0);
  v.pop_back();
  return (int)v.size() * 100 + count_true(v);
}
int b_const_index(int k) {
  std::vector<bool> v{false, true, true};
  v[0] = k > 0;
  return count_true(v);
}
int b_at(int k) {
  std::vector<bool> v{false, true};
  v.at(0) = true;
  return v.at(0) * 10 + v.at(1) + k;
}
int b_at_out_of_range(int k) {
  std::vector<bool> v{false, true};
  try {
    return v.at(2 + k);
  } catch (const std::out_of_range &) {
    return 77;
  }
}
int b_ref_assign(int k) {
  std::vector<bool> v{false, true, false};
  v[0] = v[1];
  v[2] = v[k % 2];
  return v[0] * 100 + v[1] * 10 + v[2];
}
int b_chain_assign(int k) {
  std::vector<bool> v(3, false);
  v[0] = v[2] = true;
  return v[0] * 100 + v[1] * 10 + v[2] + k;
}
int b_flip(int k) {
  std::vector<bool> v{true, false};
  v[0].flip();
  v[1].flip();
  if (k) v[1].flip();
  return v[0] * 10 + v[1];
}
int b_proxy_copy(int k) {
  std::vector<bool> v(2, false);
  auto r = v[1];
  r = true;
  return v[1] * 10 + v[0] + k;
}
int b_copy_ctor(int k) {
  std::vector<bool> v{true, false, true};
  std::vector<bool> w = v;
  w[0] = false;
  return v[0] * 100 + w[0] * 10 + (int)w.size() + k;
}
int b_copy_assign(int k) {
  std::vector<bool> v{true, true};
  std::vector<bool> w(5, false);
  w = v;
  return (int)w.size() * 10 + w[1] + k;
}
int b_move(int k) {
  std::vector<bool> v{true, false, true};
  std::vector<bool> w = std::move(v);
  std::vector<bool> u;
  u = std::move(w);
  return (int)u.size() * 10 + u[2] + k;
}
int b_assign_fill(int k) {
  std::vector<bool> v{false};
  v.assign(4, true);
  return (int)v.size() * 10 + v[3] + k;
}
int b_resize(int k) {
  std::vector<bool> v{true};
  v.resize(4, true);
  v.resize(6);
  int c = count_true(v);
  v.resize(2);
  return (int)v.size() * 100 + c * 10 + v[1] + k;
}
int b_clear_reserve(int k) {
  std::vector<bool> v{true, true};
  v.clear();
  v.reserve(100);
  v.push_back(k > 0);
  return (int)v.size() * 10 + v[0];
}
int b_swap(int k) {
  std::vector<bool> v{true};
  std::vector<bool> w{false, false, true};
  v.swap(w);
  return (int)v.size() * 100 + (int)w.size() * 10 + v[2] + k;
}
int b_eq(int k) {
  std::vector<bool> v{true, false, true};
  std::vector<bool> w{true, false, true};
  std::vector<bool> x{true, false};
  int r = (v == w) * 100 + (v == x) * 10;
  w[1] = true;
  return r + (v == w) + k;
}
int b_vec_of_vec(int k) {
  std::vector<std::vector<bool>> g(3, std::vector<bool>(4, false));
  g[1][2] = true;
  g[2][k % 4] = true;
  int c = 0;
  for (std::size_t i = 0; i < g.size(); ++i) c += count_true(g[i]);
  return c * 10 + g[1][2];
}
int b_range_ctor(int k) {
  bool a[] = {true, false, true, true};
  std::vector<bool> v(a + 1, a + 4);
  v[0] = k > 0;
  return (int)v.size() * 10 + count_true(v);
}
int b_sieve(int k) {
  int n = 100 + k;
  std::vector<bool> p(n + 1, true);
  p[0] = p[1] = false;
  for (int i = 2; i * i <= n; ++i)
    if (p[i])
      for (int j = i * i; j <= n; j += i) p[j] = false;
  return count_true(p);
}
// undefined: operator[] past the end
int u_b_index_past_end(int k) {
  std::vector<bool> v(3, true);
  return v[3 + k];
}
// undefined: a reference used after the vector reallocated
int u_b_stale_proxy(int k) {
  std::vector<bool> v(1, false);
  auto r = v[0];
  for (int i = 0; i < 200; ++i) v.push_back(true);
  r = true;
  return v[0] + k;
}
// gaps: iterators, front() and back(), flip() of the vector
int g_b_range_for(int k) {
  std::vector<bool> v{true, false, true};
  int c = 0;
  for (bool b : v) c += b;
  return c + k;
}
int g_b_front_back(int k) {
  std::vector<bool> v{true, false};
  return v.front() * 10 + v.back() + k;
}
int g_b_flip_all(int k) {
  std::vector<bool> v{true, false};
  v.flip();
  return v[0] * 10 + v[1] + k;
}

// value-initialization of polymorphic objects
struct Poly {
  int x;
  virtual int f() const { return 7; }
};
struct PolyD : Poly {
  int y;
  int f() const override { return 9; }
};
struct HasPoly {
  Poly p;
  int k;
};
int v_value_init_new(int k) {
  Poly *p = new Poly();
  int r = p->f() * 10 + p->x + k;
  delete p;
  return r;
}
int v_value_init_local(int k) {
  Poly a{};
  Poly b = Poly();
  const Poly &ra = a;
  return ra.f() * 100 + a.x * 10 + b.x + k;
}
int v_value_init_derived(int k) {
  PolyD d{};
  const Poly &r = d;
  return r.f() * 100 + d.x * 10 + d.y + k;
}
int v_value_init_array(int k) {
  Poly a[3]{};
  int s = 0;
  for (int i = 0; i < 3; ++i) {
    const Poly &r = a[i];
    s += r.f() + a[i].x;
  }
  return s + k;
}
// an array new of a polymorphic class, value-initialized
int v_value_init_array_new(int k) {
  Poly *a = new Poly[3]();
  int s = 0;
  for (int i = 0; i < 3; ++i) {
    const Poly &r = a[i];
    s += r.f() + a[i].x;
  }
  delete[] a;
  return s + k;
}
int v_value_init_member(int k) {
  HasPoly h{};
  const Poly &r = h.p;
  return r.f() * 100 + h.p.x * 10 + h.k + k;
}
// undefined: a virtual call through a zeroed vptr
int u_zero_vptr_call(int k) {
  Poly p{};
  std::memset((void *)&p, 0, sizeof p);
  const Poly *q = &p;
  return q->f() + k;
}
