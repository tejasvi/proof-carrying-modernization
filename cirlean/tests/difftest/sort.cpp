// std::sort of arithmetic types (run with CASES=sort_cases.txt): with std::less
// (or no comparator), libc++'s std::sort calls the library's instantiation
// std::__sort<__less<T, T>&, T*>, modelled as an ascending sort of the range
// in place; other comparators (std::greater) run the introsort inlined from
// the headers. Expected result (labelled per case in the cases file): MATCH on
// the t_* cases; UB on the u_* controls (an indeterminate element, a NaN, and
// -0.0 with +0.0 in one range, whose order is not modelled).
#include <algorithm>
#include <cmath>
#include <functional>
#include <limits>
#include <memory>
#include <vector>

template <class T>
static int cks(const T *a, int n) {
  unsigned s = 0;
  for (int i = 0; i < n; ++i) s = s * 31u + (unsigned)(long long)a[i];
  return (int)(s & 0x7fffffffu);
}

static int dcks(const double *a, int n) {
  double s = 0;
  for (int i = 0; i < n; ++i) s += a[i] * (i + 1);
  return (int)(s * 4);
}

static unsigned signs(const double *a, int n) {
  unsigned r = 0;
  for (int i = 0; i < n; ++i) {
    union { double d; unsigned long long u; } c;
    c.d = a[i];
    r = r * 2 + (unsigned)(c.u >> 63);
  }
  return r;
}

int t_sort_int(int n) {
  int a[9] = {5, -3, 9, 1, 3, 3, n, 0, -7};
  std::sort(a, a + 9);
  return cks(a, 9);
}

int t_sort_dups(int n) {
  int a[6] = {n, 2, n, 2, n, 2};
  std::sort(a, a + 6);
  return cks(a, 6);
}

int t_sort_empty(int n) {
  int a[3] = {3, n, 1};
  std::sort(a, a);
  std::sort(a + 1, a + 1);
  return cks(a, 3);
}

int t_sort_one(int n) {
  int a[1] = {n};
  std::sort(a, a + 1);
  return a[0];
}

int t_sort_sub(int n) {
  int a[8] = {8, 7, 6, n, 4, 3, 2, 1};
  std::sort(a + 2, a + 6);
  return cks(a, 8);
}

int t_sort_heap(int n) {
  const int N = 40;
  std::unique_ptr<int[]> p(new int[N]);
  for (int i = 0; i < N; ++i) p[i] = (i * 7919 + n) % 101 - 50;
  std::sort(&p[0], &p[N]);
  int up = cks(&p[0], N);
  std::sort(&p[0], &p[N], std::greater<int>());
  return up ^ cks(&p[0], N);
}

int t_sort_vector(int n) {
  std::vector<int> v = {4, n, -1, 4, 0, 12};
  std::sort(v.data(), v.data() + v.size());
  return cks(v.data(), (int)v.size());
}

// through the iterators: libc++ unwraps them, end() included, with
// std::__to_address
int t_sort_vector_iters(int n) {
  std::vector<int> v = {4, n, -1, 4, 0, 12};
  std::sort(v.begin(), v.end());
  return cks(v.data(), (int)v.size());
}

int t_sort_types(int n) {
  unsigned char c[5] = {200, 3, (unsigned char)n, 255, 0};
  short s[4] = {-300, 7, (short)n, -1};
  unsigned u[4] = {4000000000u, 1, (unsigned)n, 77};
  long long l[3] = {-5000000000LL, 6, n};
  unsigned long long q[3] = {18000000000000000000ULL, 2, (unsigned long long)n};
  std::sort(c, c + 5);
  std::sort(s, s + 4);
  std::sort(u, u + 4);
  std::sort(l, l + 3);
  std::sort(q, q + 3);
  return cks(c, 5) ^ cks(s, 4) ^ cks(u, 4) ^ cks(l, 3) ^ cks(q, 3);
}

int t_sort_less(int n) {
  int a[5] = {3, n, 1, 4, 1};
  int b[5] = {9, 2, n, 6, 5};
  std::sort(a, a + 5, std::less<int>());
  std::sort(b, b + 5, std::less<>());
  return cks(a, 5) ^ cks(b, 5);
}

int t_sort_greater(int n) {
  int a[7] = {1, n, 5, -2, 5, 0, 8};
  std::sort(a, a + 7, std::greater<int>());
  return cks(a, 7);
}

int t_sort_double(int n) {
  double a[6] = {2.5, -1.0, (double)n, 0.0, 3.25, -7.5};
  std::sort(a, a + 6);
  return dcks(a, 6);
}

int t_sort_float(int n) {
  float a[5] = {1.5f, -0.25f, (float)n, 8.0f, -3.0f};
  std::sort(a, a + 5);
  double d[5];
  for (int i = 0; i < 5; ++i) d[i] = a[i];
  return dcks(d, 5);
}

int t_sort_negzero(int n) {
  double a[5] = {-0.0, 1.0, -0.0, -2.0, (double)n};
  std::sort(a, a + 5);
  return (int)signs(a, 5) * 1000 + dcks(a, 5);
}

int t_sort_poszero(int n) {
  double a[5] = {0.0, 1.0, 0.0, -2.0, (double)n};
  std::sort(a, a + 5);
  return (int)signs(a, 5) * 1000 + dcks(a, 5);
}

int u_sort_zeros(int n) {
  double a[4] = {0.0, -0.0, 1.0, (double)n};
  std::sort(a, a + 4);
  return (int)signs(a, 4);
}

int u_sort_nan(int n) {
  double a[3] = {1.0, std::numeric_limits<double>::quiet_NaN(), (double)n};
  std::sort(a, a + 3);
  return 0;
}

int u_sort_uninit(int n) {
  int a[4];
  a[0] = n;
  a[1] = 1;
  a[3] = 2;
  std::sort(a, a + 4);
  return a[0];
}
