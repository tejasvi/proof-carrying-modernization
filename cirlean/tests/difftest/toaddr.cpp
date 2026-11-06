// Algorithms on std::vector and std::string iterators (run with
// CASES=toaddr_cases.txt): libc++ unwraps contiguous iterators to pointers
// with std::__to_address (and std::to_address), end() included, which gives
// the pointer the iterator holds without a dereference. Expected result
// (labelled per case in the cases file): MATCH on the t_* cases; UB on the
// u_* control (a dereference of end()).
#include <algorithm>
#include <iterator>
#include <memory>
#include <string>
#include <vector>

static int cks(const std::vector<int> &v) {
  unsigned s = 0;
  for (int x : v) s = s * 31u + (unsigned)x;
  return (int)(s & 0x7fffffffu);
}

int t_sort_iters(int n) {
  std::vector<int> v = {5, n, -2, 9, 0, 5};
  std::sort(v.begin(), v.end());
  return cks(v);
}

int t_sort_part(int n) {
  std::vector<int> v = {9, 8, n, 6, 5, 4};
  std::sort(v.begin() + 1, v.end() - 1);
  return cks(v);
}

int t_sort_empty(int n) {
  std::vector<int> v;
  std::sort(v.begin(), v.end());
  return (int)v.size() + n;
}

int t_sort_string(int n) {
  std::string s = "dcbax";
  s[4] = (char)('a' + n);
  std::sort(s.begin(), s.end());
  return s[0] * 1000 + s[4];
}

int t_copy_back(int n) {
  std::vector<int> a = {1, 2, n, 4};
  std::vector<int> b = {7};
  std::copy(a.begin(), a.end(), std::back_inserter(b));
  return cks(b);
}

// into the storage of another vector: libc++ copies a trivially copyable range
// with memmove (over std::vector storage, see vecmem.cpp)
int t_copy_storage(int n) {
  std::vector<int> a = {1, 2, n, 4};
  std::vector<int> b(4);
  std::copy(a.begin(), a.end(), b.begin());
  return cks(b);
}

int t_fill_reverse(int n) {
  std::vector<int> v(5);
  std::fill(v.begin(), v.end(), n);
  v[0] = 1;
  std::reverse(v.begin(), v.end());
  return cks(v);
}

int t_to_address_end(int n) {
  std::vector<int> v = {1, 2, 3, n};
  int *e = std::to_address(v.end());
  return (int)(e - v.data()) * 10 + *(e - 1);
}

int u_deref_end(int n) {
  std::vector<int> v = {1, 2, n};
  return *v.end();
}
