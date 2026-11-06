// std::vector::assign and operator=(initializer_list); std::string's swap, iterator-range
// constructor, operator+ and compare (run with CASES=contb3_cases.txt). Expected result
// (labelled per case in the cases file): MATCH, or UB from cirrun on the u_ cases, which
// break a precondition or read an indeterminate character (native runs print the result
// of libc++'s code), and on the g_ gaps. Comparisons return the sign only: compare's value
// is unspecified beyond it.
#include <string>
#include <utility>
#include <vector>

static int sign(int r) { return (r > 0) - (r < 0); }

// vector::assign(n, x): grow, shrink, empty; elements of other types
int a_fill_grow(int k) {
  std::vector<int> v = {1, 2, 3};
  v.assign(5, 7 + k);
  return (int)v.size() * 100 + v[0] + v[4];
}
int a_fill_shrink(int k) {
  std::vector<int> v = {1, 2, 3, 4, 5, 6};
  v.assign(2, k - 3);
  return (int)v.size() * 100 + v[1];
}
int a_fill_zero(int k) {
  std::vector<int> v = {1, 2, 3};
  v.assign(0, 9);
  return (int)v.size() * 100 + (int)v.empty() + k;
}
int a_fill_ulong(int k) {
  std::vector<unsigned long> v;
  v.assign(4, 3);
  for (unsigned long i = 0; i < v.size(); ++i) v[i] += i * (unsigned long)k;
  return (int)(v[3] * 10 + v.size());
}
int a_fill_double(int k) {
  std::vector<double> v(2, 1.5);
  v.assign(3, 0.25 * k);
  return (int)((v[0] + v[2]) * 100) + (int)v.size();
}
// the value from another vector
int a_fill_from_other(int k) {
  std::vector<int> w = {4, 5, 6};
  std::vector<int> v = {1};
  v.assign(3, w[k % 3]);
  return v[2] * 10 + (int)v.size();
}
// undefined: the value is an element of the vector itself ([sequence.reqmts], a.assign(n, t))
int u_fill_self_elem(int k) {
  std::vector<int> v = {4, 5, 6};
  v.assign(2, v[k % 3]);
  return v[1] * 10 + (int)v.size();
}
// undefined: a pointer to an element read after assign invalidated it
int u_fill_stale_ptr(int k) {
  std::vector<int> v = {4, 5, 6};
  int *p = &v[1];
  v.assign(2, 1);
  return *p + k;
}

// vector::operator=(std::initializer_list<T>)
int a_list_assign(int k) {
  std::vector<long> v;
  v = {3, 4, 5 + k};
  return (int)(v.size() * 100 + v[2]);
}
int a_list_shrink(int k) {
  std::vector<int> v = {1, 2, 3, 4};
  v = {7 + k};
  return (int)v.size() * 100 + v[0];
}
int a_list_empty(int k) {
  std::vector<int> v = {1, 2, 3, 4};
  v = {};
  return (int)v.size() * 100 + k;
}
int a_list_result(int k) {
  std::vector<char> v;
  return (int)(v = {'a', 'b', char('c' + k)}).size() * 1000 + v[2];
}

// vector::assign(first, last): pointers and vector iterators
int a_range_ptrs(int k) {
  int a[] = {10, 20, 30, 40, 50};
  std::vector<int> v = {1, 2};
  v.assign(a + 1, a + 4 + k % 2);
  return (int)v.size() * 1000 + v[0] + v.back();
}
int a_range_iters(int k) {
  std::vector<int> w = {6, 7, 8, 9};
  std::vector<int> v;
  v.assign(w.begin() + k % 2, w.end());
  return (int)v.size() * 100 + v[0];
}
int a_range_empty(int k) {
  const long a[] = {1, 2};
  std::vector<long> v = {5, 6, 7};
  v.assign(a, a);
  return (int)v.size() * 100 + k;
}
// assign(std::initializer_list<T>): libc++'s body calls assign(first, last) with the list's begin and end
int a_assign_list(int k) {
  std::vector<int> v = {9};
  v.assign({1, 2, 3 + k});
  return (int)v.size() * 100 + v[2];
}
// undefined: the range is in the vector itself ([sequence.reqmts], a.assign(i, j))
int u_range_self(int k) {
  std::vector<int> v = {1, 2, 3, 4};
  v.assign(v.begin() + 1 + k % 2, v.end());
  return (int)v.size() * 100 + v[0];
}

// basic_string::swap and std::swap of strings
int s_swap(int k) {
  std::string a = "abc", b = "de";
  a.swap(b);
  return (int)a.size() * 1000 + (int)b.size() * 100 + a[k % 2];
}
int s_std_swap(int k) {
  std::string a = "x", b = "this string is longer than the short buffer";
  std::swap(a, b);
  return (int)a.size() * 1000 + (int)b.size() * 100 + b[0] + k;
}

// basic_string(n, c): libc++'s constructor (its body calls __init(n, c) from libc++'s library)
int s_fill(int k) {
  std::string s(3 + k, 'x');
  return (int)s.size() * 1000 + s[0] + s[s.size() - 1];
}
int s_fill_empty(int k) {
  std::string s(0, 'y');
  return (int)s.size() * 100 + (int)s.empty() + k;
}
int s_fill_long(int k) {
  std::string s(40 + k, 'z');
  s += "!";
  return (int)s.size() * 1000 + s[40 + k];
}
int s_fill_compare(int k) {
  std::string a(2, 'a'), b(2 + k, 'a');
  return sign(a.compare(b)) * 10 + (a == b);
}

// basic_string(first, last[, alloc]): char pointers, string and vector iterators, reverse iterators
int r_ptrs(int k) {
  const char *s = "hello";
  std::string t(s + 1, s + 4 + k % 2);
  return (int)t.size() * 1000 + t[0] + t[t.size() - 1];
}
int r_iters(int k) {
  std::string u = "world";
  std::string t(u.begin() + k % 3, u.end());
  return (int)t.size() * 1000 + t[0];
}
int r_reverse(int k) {
  std::string u = "abcdef";
  std::string t(u.rbegin() + k % 2, u.rend());
  return (int)t.size() * 1000 + t[0] * 10 + (t[t.size() - 1] == 'a');
}
int r_reverse_const(int k) {
  const std::string u = "xyz";
  std::string t(u.rbegin(), u.rend());
  return (int)t.size() * 1000 + t[0] + t[2] * (k + 1);
}
int r_vector_chars(int k) {
  std::vector<char> v = {'p', 'q', 'r'};
  std::string t(v.begin(), v.end() - k % 2);
  return (int)t.size() * 1000 + t[t.size() - 1];
}
int r_alloc(int k) {
  const char *s = "abcdef";
  std::string t(s, s + 3, std::allocator<char>());
  return (int)t.size() * 1000 + t[2] + k;
}
int r_empty(int k) {
  const char *s = "abc";
  std::string t(s + 1, s + 1);
  return (int)t.size() * 100 + (int)t.empty() + k;
}
// undefined: an indeterminate character in the range is read ([basic.indet], char_traits::assign)
int u_range_indeterminate(int k) {
  char buf[4];
  buf[0] = 'a';
  std::string t(buf, buf + 2 + k % 2);
  return (int)t.size();
}

// operator+: libc++'s __concatenate_strings (strings, C strings, characters) and its exported
// operator+(const char*, const string&)
int p_strings(int k) {
  std::string a = "ab", b = "cde";
  std::string c = a + b;
  return (int)c.size() * 1000 + c[2 + k % 3];
}
int p_string_cstr(int k) {
  std::string a = "ab";
  std::string c = a + "xyz";
  return (int)c.size() * 1000 + c[k % 5];
}
int p_cstr_string(int k) {
  std::string a = "ab";
  std::string c = "xyz" + a;
  return (int)c.size() * 1000 + c[k % 5];
}
int p_string_char(int k) {
  std::string a = "ab";
  std::string c = a + (char)('p' + k);
  return (int)c.size() * 1000 + c[2];
}
int p_char_string(int k) {
  std::string a = "ab";
  std::string c = (char)('p' + k) + a;
  return (int)c.size() * 1000 + c[0];
}
int p_rvalue(int k) {
  std::string c = std::string("ab") + "cd";
  return (int)c.size() * 1000 + c[3] + k;
}
int p_chain(int k) {
  std::string a = "a", b = "bc";
  std::string c = a + b + "def" + 'g' + a;
  return (int)c.size() * 1000 + c[k % 8];
}
int p_long(int k) {
  std::string a = "a string longer than libc++'s short buffer";
  std::string c = a + a;
  return (int)c.size() * 1000 + c[44 + k];
}
int p_empty(int k) {
  std::string a = "abc";
  std::string c = std::string() + a + std::string();
  return (int)c.size() * 1000 + c[k % 3];
}

// compare and operator<: of strings through char_traits::compare (memcmp over their characters),
// compare(const char*) and compare(pos, n1, const char*, n2) (libc++'s library; operator== with a C string)
int c_less(int k) {
  std::string a = "abc", b = k ? "abd" : "ab";
  return (a < b) + 2 * (b < a) + 4 * (a < a);
}
int c_compare(int k) {
  std::string a = "abc", b = k ? "abd" : "abc";
  return sign(a.compare(b)) * 10 + sign(b.compare(a));
}
int c_compare_cstr(int k) {
  std::string a = "abc";
  return sign(a.compare("abc")) * 100 + sign(a.compare(k ? "abcd" : "ab")) * 10 + sign(a.compare("b"));
}
int c_eq_cstr(int k) {
  std::string a = "abc";
  return (a == "abc") * 100 + (a == (k ? "ab" : "abd")) * 10 + ("abc" == a);
}
int c_compare_sub(int k) {
  std::string a = "abcd";
  return sign(a.compare(1, 2, "bcx", 2)) * 100 + sign(a.compare(1, 5, "bc", 2)) * 10 +
         sign(a.compare(k % 4, 1, "c", 1));
}
// characters as unsigned char: '\xe9' after 'a'
int c_unsigned(int k) {
  std::string a = "\xe9", b = "a";
  return (a < b) * 100 + sign(a.compare("a")) * 10 + sign(a.compare(0, 1, "a", 1)) + k;
}
// out_of_range: pos1 > size()
int c_compare_pos_throw(int k) {
  std::string a = "ab";
  return a.compare(3 + k, 1, "x", 1);
}
// only the characters compared are read: s[1..3] stay indeterminate
int c_compare_sub_short(int k) {
  char buf[4];
  buf[0] = 'a';
  std::string a = "a";
  return sign(a.compare(0, 1, buf, 4)) + k;
}
// undefined: compare(const char*) with an array that has no terminator
int u_compare_unterminated(int k) {
  char buf[3] = {'a', 'b', 'c'};
  std::string a = "abc";
  return sign(a.compare(buf)) + k;
}
// gap: a string's c_str() as the C string of compare(const char*) and of operator+(const char*,
// const string&); the C string models read char arrays, not a string's characters
int g_compare_c_str(int k) {
  std::string a = "abc", b = k ? "abd" : "abc";
  return sign(a.compare(b.c_str()));
}
int g_plus_c_str(int k) {
  std::string a = "ab", b = "xy";
  std::string c = b.c_str() + a;
  return (int)c.size() * 1000 + c[k % 4];
}
