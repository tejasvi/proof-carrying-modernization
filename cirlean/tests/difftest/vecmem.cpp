// memmove, memcpy, memset and memcmp over the storage of std::vector and
// std::string (run with CASES=vecmem_cases.txt): the live elements, of the
// element type the container's type names, as libc++'s std::copy (memmove of a
// trivially copyable range), std::equal and the containers' == (memcmp of
// trivially comparable elements) and direct calls on data() use them.
// Expected result (labelled per case in the cases file): MATCH on the t_*
// cases; UB on the u_* controls (overlapping memcpy, a range past the live
// elements, part of an element, an indeterminate element).
#include <algorithm>
#include <cstring>
#include <string>
#include <vector>

static int cks(const std::vector<int> &v) {
  unsigned s = 0;
  for (int x : v) s = s * 31u + (unsigned)x;
  return (int)(s & 0x7fffffffu);
}

static int sign(int r) { return (r > 0) - (r < 0); }

int t_copy(int n) {
  std::vector<int> a = {1, 2, n, 4};
  std::vector<int> b(4);
  std::copy(a.begin(), a.end(), b.begin());
  return cks(b);
}

int t_copy_within(int n) {
  std::vector<int> v = {1, 2, 3, n, 5};
  std::copy(v.begin() + 1, v.end(), v.begin());
  return cks(v);
}

int t_copy_backward(int n) {
  std::vector<int> v = {1, 2, 3, n, 5};
  std::copy_backward(v.begin(), v.end() - 1, v.end());
  return cks(v);
}

int t_copy_double(int n) {
  std::vector<double> a = {0.5, -2.0, n * 1.25};
  std::vector<double> b(3);
  std::copy(a.begin(), a.end(), b.begin());
  return (int)((b[0] + b[1] * 10 + b[2] * 100) * 8);
}

int t_eq(int n) {
  std::vector<int> a = {1, 2, n};
  std::vector<int> b = {1, 2, n};
  std::vector<int> c = {1, 2, n + 1};
  return (a == b) * 10 + (a == c);
}

int t_equal(int n) {
  std::vector<int> a = {7, n, 9};
  std::vector<int> b = {7, n, 9, 10};
  return std::equal(a.begin(), a.end(), b.begin()) ? n : -n;
}

int t_memcmp(int n) {
  std::vector<int> a = {1, 256, n};
  std::vector<int> b = {1, 1, n};
  int r1 = std::memcmp(a.data(), b.data(), 3 * sizeof(int));
  int r2 = std::memcmp(a.data(), a.data(), 3 * sizeof(int));
  return sign(r1) * 10 + sign(r2);
}

int t_memcpy_memset(int n) {
  std::vector<int> a = {4, 5, n};
  std::vector<int> b(3);
  std::memcpy(b.data(), a.data(), 3 * sizeof(int));
  std::vector<int> c = {9, 9, 9};
  std::memset(c.data(), 0, 2 * sizeof(int));
  return cks(b) ^ cks(c);
}

int t_string_copy(int n) {
  std::string s = "hello";
  std::string t = "xxxxx";
  s[0] = (char)('a' + n);
  std::copy(s.begin(), s.end(), t.begin());
  return t[0] * 1000 + t[4];
}

int t_string_eq(int n) {
  std::string s = "abc";
  std::string t = "abc";
  std::string u = "abd";
  return (s == t) * 100 + (s == u) * 10 + (s < u) + n;
}

int u_memcpy_overlap(int n) {
  std::vector<int> v = {1, 2, n, 4};
  std::memcpy(v.data() + 1, v.data(), 2 * sizeof(int));
  return cks(v);
}

int u_past_size(int n) {
  std::vector<int> a = {1, 2, n};
  std::vector<int> b(4);
  std::memcpy(b.data(), a.data(), 4 * sizeof(int));
  return cks(b);
}

int u_part_element(int n) {
  std::vector<int> v = {1, 2, 3};
  short x = (short)n;
  std::memcpy(v.data(), &x, sizeof x);
  return v[0];
}

int u_indeterminate(int n) {
  int arr[3];
  arr[0] = n;
  std::vector<int> v(3);
  std::memcpy(v.data(), arr, sizeof arr);
  return v[1];
}
