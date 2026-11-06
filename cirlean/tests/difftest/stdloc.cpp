// Which calls are the C++ library's own (run with CASES=stdloc_cases.txt): its functions' bodies,
// by namespace and by the location of the definition in the library's headers, not the
// program's code in namespace std (rog's soundness audit at next3 81dd03c, finding X1, n3c3.cpp).
// Expected result (labelled per case in the cases file): UB from cirrun where the program calls
// memcpy/memcmp/memset with length 0 and a null pointer, also in its own specializations of
// standard class templates ([namespace.std]p2) and in a function it adds to std; MATCH for the
// library's own empty copy.
#include <algorithm>
#include <cstring>
#include <functional>
#include <vector>

struct K { int v; };
// a program's explicit specialization of a standard class template, allowed ([namespace.std]p2);
// its body is the program's code: memcpy with a null source and length 0 is undefined (C11 7.24.1p2)
template <> struct std::hash<K> {
  std::size_t operator()(const K &k) const noexcept {
    char buf[4] = {1, 2, 3, 4};
    std::memcpy(buf, (const void *)0, (std::size_t)(k.v & 0));
    return (std::size_t)(k.v + buf[0]);
  }
};
int c3_hash_specialization(int k) {
  K key{k + 5};
  return (int)std::hash<K>()(key);
}
// the same in std::less<K>, with memcmp
template <> struct std::less<K> {
  bool operator()(const K &a, const K &b) const {
    return std::memcmp((const void *)0, (const void *)0, (std::size_t)(a.v & 0)) == 0 && a.v < b.v;
  }
};
int c3_less_specialization(int k) {
  K a{1}, b{2 + k};
  return std::less<K>()(a, b) ? 7 : 8;
}
// a function the program adds to namespace std ([namespace.std]p1: undefined anyway)
namespace std {
int c3_added_helper(int k) {
  char buf[4] = {1, 2, 3, 4};
  std::memset((void *)0, 0, (std::size_t)(k & 0));
  return buf[1] + k;
}
}
int c3_added_to_std(int k) { return std::c3_added_helper(k); }
// controls: the program's own functions keep the checks
template <class T> std::vector<T> c3_make(T v) {
  char buf[4] = {1, 2, 3, 4};
  std::memcpy(buf, (const void *)0, (std::size_t)(v & 0));
  return std::vector<T>(1, v + buf[0]);
}
int c3_template_returning_std(int k) { return c3_make<int>(k + 1)[0]; }
struct Fn {
  void operator()(int &x) const {
    char buf[4] = {1, 2, 3, 4};
    std::memcpy(buf, (const void *)0, (std::size_t)(x & 0));
    x += buf[2];
  }
};
int c3_functor_in_for_each(int k) {
  std::vector<int> v = {k, k + 1};
  std::for_each(v.begin(), v.end(), Fn());
  return v[0] + v[1];
}
int c3_lambda_in_for_each(int k) {
  std::vector<int> v = {k, k + 1};
  std::for_each(v.begin(), v.end(), [](int &x) {
    char buf[4] = {1, 2, 3, 4};
    std::memcpy(buf, (const void *)0, (std::size_t)(x & 0));
    x += buf[3];
  });
  return v[0] + v[1];
}
// the library's own empty copy through null pointers (defined)
int c3_library_empty_copy(int k) {
  int *p = nullptr;
  int *q = std::copy(p, p, p);
  return (q == nullptr) + k;
}
