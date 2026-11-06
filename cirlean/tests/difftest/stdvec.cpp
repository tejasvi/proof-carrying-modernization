// std::vector<int> through the native models.
#include <vector>
#include <utility>

int t_vec_push_index(int n) {
  std::vector<int> v;
  for (int i = 0; i < n; ++i) v.push_back(i * i);
  int s = 0;
  for (std::size_t i = 0; i < v.size(); ++i) s += v[i];
  return s * 10 + (int)v.size();
}

int t_vec_rangefor(int n) {
  std::vector<int> v{3, 1, 4, 1, 5};
  v.push_back(n);
  int s = 0;
  for (int x : v) s = s * 2 + x;
  return s;
}

int t_vec_iter(int n) {
  std::vector<int> v(5, n);
  v[2] = 7;
  int s = 0;
  for (auto it = v.begin(); it != v.end(); ++it) s += *it;
  auto e = v.end();
  --e;
  return s * 100 + *e + (int)(v.end() - v.begin());
}

int t_vec_front_back_pop(int n) {
  std::vector<int> v;
  for (int i = 1; i <= n; ++i) v.push_back(i);
  int r = v.front() * 1000 + v.back();
  v.pop_back();
  r += v.back() * 10;
  return r;
}

int t_vec_copy_move(int n) {
  std::vector<int> a{1, 2, 3};
  a.push_back(n);
  std::vector<int> b = a;
  b[0] = 100;
  std::vector<int> c = std::move(b);
  return a[0] + c[0] + (int)c.size() * 1000 + (int)b.size() * 10000;
}

int t_vec_clear_resize(int n) {
  std::vector<int> v(3);
  v.resize(n, 2);
  int s = 0;
  for (int x : v) s += x;
  v.clear();
  return s * 10 + (int)v.empty();
}

int t_vec_at_throw(int i) {
  std::vector<int> v{10, 20, 30};
  try {
    return v.at(i);
  } catch (...) {
    return -1;
  }
}

static int sum_ref(const std::vector<int> &v) {
  int s = 0;
  for (int x : v) s += x;
  return s;
}
int t_vec_param(int n) {
  std::vector<int> v;
  for (int i = 0; i < n; ++i) v.push_back(2 * i + 1);
  return sum_ref(v);
}

int t_vec_data_swap(int n) {
  std::vector<int> a{1, 2};
  std::vector<int> b{5, 6, 7};
  a.swap(b);
  int *p = a.data();
  return p[0] * 100 + p[2] + (int)b.size() * n;
}
