// The C++ standard library's own <string.h> calls with length 0 (run with CASES=stdmem_cases.txt).
// libc++ relocates, copies and compares empty ranges with memmove/memcpy/memcmp through null
// pointers, as its platform allows; C11 7.24.1p2 (a valid pointer also with length 0) binds the
// program's calls, not the implementation's own. Expected result (labelled per case in the cases
// file): MATCH on the l_ cases (the library's calls) and the c_ case, UB from cirrun on the u_
// cases (the program's own calls with length 0 and a null or dangling pointer; native runs print
// glibc's result).
#include <algorithm>
#include <cstring>
#include <utility>
#include <vector>

// a vector whose element type has no model: its first growth relocates the empty buffer, null
// pointers, with memmove
int l_relocate_empty(int k) {
  std::vector<std::pair<int, int>> v;
  v.push_back({1 + k, 2});
  v.push_back({3, 4});
  v.push_back({5, 6});
  return v[2].second * 100 + v[0].first * 10 + (int)v.size();
}
// a vector of vectors, as graph programs build adjacency lists
int l_vec_of_vecs(int k) {
  std::vector<std::vector<int>> g;
  g.push_back({1, 2});
  g.push_back({3 + k});
  return g[1][0] * 10 + (int)g[0].size() + (int)g.size() * 100;
}
// std::copy of an empty range of null pointers: memmove(nullptr, nullptr, 0)
int l_copy_empty(int k) {
  int *p = nullptr;
  int *r = std::copy(p, p, p);
  return (r == nullptr) + k;
}
// std::equal of an empty range of null pointers: memcmp(nullptr, nullptr, 0)
int l_equal_empty(int k) {
  const int *p = nullptr;
  return (int)std::equal(p, p, p) + k;
}
// the program's own calls with length 0 and a null or dangling pointer (C11 7.24.1p2)
int u_memcpy_null(int k) {
  char buf[4] = {1, 2, 3, 4};
  const char *src = k ? buf : nullptr;
  memcpy(buf, src, 0);
  return buf[0];
}
int u_memmove_null(int k) {
  char buf[4] = {1, 2, 3, 4};
  char *dst = k ? buf : nullptr;
  memmove(dst, buf, 0);
  return buf[1];
}
int u_memset_null(int k) {
  char *dst = k ? new char[1] : nullptr;
  memset(dst, 0, 0);
  return dst == nullptr;
}
int u_memcmp_null(int k) {
  char buf[2] = {1, 2};
  const char *a = k ? buf : nullptr;
  return memcmp(a, buf, 0);
}
int u_memcpy_dangling(int k) {
  char buf[4] = {1, 2, 3, 4};
  char *p = new char[4];
  delete[] p;
  memcpy(buf, p, 0);
  return buf[2] + k;
}
// the program's own call with length 0 and valid pointers: defined
int c_memcpy_zero(int k) {
  char a[2] = {5, 6}, b[2] = {7, 8};
  memcpy(a, b, 0);
  return a[k % 2];
}
