// Containers of containers from initializer lists (run with CASES=contb_cases.txt).
// CIR stores the address of an initializer_list's backing array object as its
// begin pointer, and strides from it are byte views of that array; for a vector
// of vectors or of strings, libc++'s own code walks the list and hands these
// pointers to the modelled element constructors and members. Expected result
// (labelled per case in the cases file): MATCH on the c_ cases, UB from cirrun on
// the g_ gaps (native runs print the GCC result).
#include <cstring>
#include <string>
#include <vector>

// a vector of vectors from a list of lists
int c_vec_of_vecs(int k) {
  std::vector<std::vector<int>> v = {{1, 2}, {3, 4, 5}, {6}};
  return v[1][2] + (int)v.size() * 10 + (int)v[k % 3].size() * 100;
}
// a vector of strings from a list of strings
int c_vec_of_strings(int k) {
  std::vector<std::string> v = {"ab", "cde", "f"};
  return (int)v[1].size() * 10 + v[2][0] + (int)v[k % 3].size() * 1000;
}
// a copy of a vector of vectors made from a list
int c_copy_vec_of_vecs(int k) {
  std::vector<std::vector<int>> v = {{1}, {2, 3}};
  std::vector<std::vector<int>> w = v;
  return w[1][1] * 10 + w[0][0] + k;
}
// a range-for over a list of strings: size, operator[] and c_str of its elements
int c_list_of_strings(int k) {
  int total = 0;
  for (const std::string &s : {std::string("ab"), std::string("cde"), std::string("f")})
    total += (int)s.size() * 100 + s[0] + *s.c_str() * 1000;
  return total + k;
}
// a range-for over a list of vectors and over each vector's elements
int c_list_of_vecs(int k) {
  int total = 0;
  for (const std::vector<int> &r : {std::vector<int>{1, 2}, std::vector<int>{30}, std::vector<int>{400, 5}})
    for (int x : r) total += x;
  return total + k;
}
// a vector of vectors of strings; the inner vectors are libc++ objects (no model for a vector of
// strings), whose copy constructor reads their members through the list's begin
int c_nested_strings(int k) {
  std::vector<std::vector<std::string>> v = {{"a", "bc"}, {"def", "g"}};
  return (int)v[0][1].size() * 10 + (int)v[1][0].size() + (int)v[1][1].size() * 100 + k;
}
// initializer_lists of scalars and records, read by the program's own code and by libc++'s

// a range-for over an initializer_list of ints
int c_initlist_loop(int k) {
  std::initializer_list<int> il = {1, 20, 300};
  int s = 0;
  for (int x : il) s += x;
  return s + (int)il.size() * 1000 + il.begin()[2 % (k + 3)];
}
// a vector of pairs from a list (graph_lowest_common_ancestor's pattern)
int c_pair_list(int k) {
  std::vector<std::pair<int, int>> v = {{7, 1}, {1, 5}, {1, 3}};
  return v[1].second * 100 + v[2].first * 10 + v[k % 3].second;
}
// a vector of structs of longs from a list (math_ncr_modulo_p's pattern)
struct Case5 { long a, b, c, d, e; };
int c_record_list(int k) {
  std::vector<Case5> v = {{1, 2, 3, 4, 5}, {6, 7, 8, 9, 10}};
  return (int)(v[1].e * 100 + v[0].c * 10 + v[k % 2].a);
}

// C++ null pointer arithmetic ([expr.add]p4.1, p5.1); contbc.c has the C versions (undefined)

// the difference of two null pointers: 0
int n_null_diff(int k) {
  int *p = nullptr, *q = nullptr;
  return (int)(p - q) + k;
}
// a null pointer plus k: null for k = 0 (k = 1 is undefined)
int n_null_plus(int k) {
  int *p = nullptr;
  int *r = p + k;
  return r == nullptr;
}
// a null pointer minus 0: null
int n_null_minus_zero(int k) {
  int *p = nullptr;
  int *r = p - k;
  return (r == nullptr) * 10 + k;
}
// the size of an empty vector of strings (libc++'s own code: end - begin, both null)
int n_empty_vec_of_strings(int k) {
  std::vector<std::string> v;
  return (int)v.size() + (int)v.empty() * 10 + k;
}

// std::vector::emplace_back (one element: push_back's path, returning a reference)

// emplace_back of rvalues; the returned reference written through
int e_emplace_back(int k) {
  std::vector<int> v;
  v.emplace_back(3);
  int &r = v.emplace_back(4 + k);
  r += 10;
  return v[0] * 100 + v[1];
}
// emplace_back of an lvalue
int e_emplace_lvalue(int k) {
  std::vector<unsigned> v;
  unsigned x = 7 + k;
  v.emplace_back(x);
  v.emplace_back(x + 1);
  return (int)(v.back() * 10 + v.size());
}
// gap: emplace_back of an int into a vector of long (a converting construction: not modelled)
int g_emplace_convert(int k) {
  std::vector<long> v;
  v.emplace_back(5 + k);
  return (int)v[0];
}
// gap: emplace_back with no argument (value-initialization: not modelled)
int g_emplace_none(int k) {
  std::vector<int> v;
  v.emplace_back();
  return (int)v.size() * 10 + v[0] + k;
}

// gap: a list of one vector; the copy goes into a buffer of one element, a heap object of the
// element's type that is no array element, and libc++ steps past it (UB "pointer arithmetic out
// of bounds": a lone object as an array of one is bytes phase 1b)
int g_one_vec_list(int k) {
  std::vector<std::vector<int>> v = {{7, 8}};
  return v[0][1] + k;
}
// a list of structs with string members; the implicit copy constructor's member accesses go
// through the list's begin
struct TC { std::string a; std::string b; int n; };
int c_struct_list(int k) {
  std::vector<TC> v = {{"x", "yz", 1}, {"p", "q", 2}};
  return (int)v[0].b.size() + v[1].n * 10 + k;
}
