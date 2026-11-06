// std::string::reserve (Shootout-C++ strcat) and fread from standard input (Shootout-C++ wordfreq),
// run with CASES=gaps4_cases.txt. reserve keeps the characters; the capacity is not modelled, so as
// for a vector every pointer into the string is invalidated. Standard input is at its end (it is
// /dev/null natively): fread reads nothing and returns 0. Expected result (labelled per case in the
// cases file): MATCH, or UB from cirrun on the u_ cases (a pointer into the string used after
// reserve; a null pointer or a pointer that is no stream given to fread, C11 7.1.4p1).
#include <cstdio>
#include <string>

int t_reserve(int k) {
  std::string s = "ab";
  s.reserve(100 + k);
  s += "cd";
  return (int) s.size() * 1000 + s[3] + k;
}

// as Shootout's strcat.cpp: the capacity doubled with reserve while appending
int t_reserve_loop(int k) {
  std::string str;
  size_t capacity = 31;
  str.reserve(capacity);
  size_t newLength = 6;
  for (int i = 0; i < 40 + k; i++) {
    if (newLength > capacity) {
      capacity *= 2;
      str.reserve(capacity);
    }
    str += "hello\n";
    newLength += 6;
  }
  return (int) str.length();
}

// undefined: a pointer into the string used after reserve (natively, reserving 1000 characters
// moves a short string out of its inline buffer)
int u_reserve_ptr(int k) {
  std::string s = "abc";
  const char *p = s.c_str();
  s.reserve(1000);
  return p[1] + k;
}

int t_fread_stdin(int k) {
  char buf[16];
  buf[0] = 'x';
  size_t r = fread(buf, 1, sizeof buf, stdin);
  return (int) r * 1000 + buf[0] + k;
}

int t_fread_zero(int k) {
  char buf[4] = {'a', 'b', 'c', 'd'};
  return (int) fread(buf, 0, 4, stdin) * 1000 + buf[2] + k;
}

// undefined: a null pointer (C11 7.1.4p1)
int u_fread_null(int k) {
  return (int) fread(nullptr, 1, 4, stdin) + k;
}
