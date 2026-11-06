// Constant-initialized global std::vector objects, which hold libc++'s members of an empty vector
// without a constructor call, and a polymorphic global zeroed before its constructor runs (run with
// CASES=vecfix_cases.txt; vecfix.cpp has the other cases, apart from these globals, whose destructors
// run at every case's exit). Expected result (labelled per case in the cases file): MATCH, or UB from
// cirrun on the u_ case.
#include <cstddef>
#include <vector>

static std::vector<int> g_v;
static std::vector<double> g_d;
static std::vector<int> g_arr[3];
struct Holder {
  int n;
  std::vector<int> v;
};
static Holder g_h;
std::vector<long> g_ext;
static std::vector<bool> g_bits;

int e_global_untouched(int k) { return (int)g_v.size() * 10 + (int)g_v.empty() + k; }
int e_global_push(int k) {
  g_v.push_back(k + 1);
  g_v.push_back(k + 2);
  return (int)g_v.size() * 100 + g_v[0] + g_v[1];
}
int e_global_begin_end(int k) {
  int s = 0;
  for (int x : g_v) s += x;
  return s * 10 + (g_v.begin() == g_v.end()) + k;
}
int e_global_data(int k) {
  (void)g_v.data();
  g_v.push_back(5 + k);
  return *g_v.data();
}
int e_global_clear(int k) {
  g_v.clear();
  g_v.push_back(k);
  return (int)g_v.size() * 10 + g_v[0];
}
int e_global_resize(int k) {
  g_v.resize(3);
  g_v[2] = k + 4;
  return (int)g_v.size() * 10 + g_v[0] + g_v[2];
}
int e_global_assign(int k) {
  g_v = std::vector<int>{1, 2, k};
  return (int)g_v.size() * 10 + g_v[2];
}
int e_global_copy_from(int k) {
  std::vector<int> w = g_v;
  w.push_back(k);
  return (int)w.size() * 10 + (int)g_v.size();
}
int e_global_copy_to(int k) {
  std::vector<int> w = {4, 5};
  g_v = w;
  return (int)g_v.size() * 10 + g_v[1] + k;
}
int e_global_swap(int k) {
  std::vector<int> w = {7, 8, 9};
  g_v.swap(w);
  return (int)g_v.size() * 100 + (int)w.size() * 10 + g_v[0] - 7 + k;
}
int e_global_double(int k) {
  g_d.push_back(0.5 * k);
  g_d.push_back(1.5);
  return (int)((g_d[0] + g_d[1]) * 10) + (int)g_d.size();
}
int e_global_array(int k) {
  g_arr[1].push_back(k + 3);
  return (int)g_arr[0].size() * 100 + (int)g_arr[1].size() * 10 + g_arr[1][0];
}
int e_global_member(int k) {
  g_h.v.push_back(k + 6);
  g_h.n = (int)g_h.v.size();
  return g_h.n * 10 + g_h.v[0];
}
int e_extern_global(int k) {
  g_ext.push_back(k);
  g_ext.push_back(2L * k + 1);
  return (int)(g_ext[0] + g_ext[1]) * 10 + (int)g_ext.size();
}
int e_global_bool(int k) {
  g_bits.push_back(true);
  g_bits.push_back(k > 0);
  int c = 0;
  for (std::size_t i = 0; i < g_bits.size(); ++i) c += g_bits[i];
  return (int)g_bits.size() * 10 + c;
}
// undefined: an element of a vector that has none
int u_global_index_empty(int k) { return g_v[0] + k; }

// a polymorphic global whose constructor (a dynamic initializer) leaves a member to the
// zero-initialization of static storage
struct Counter {
  int hits;
  virtual int get() const { return hits; }
  Counter() {}
};
static Counter g_counter;
int v_global_zero_member(int k) {
  const Counter &r = g_counter;
  return r.get() * 10 + k;
}
