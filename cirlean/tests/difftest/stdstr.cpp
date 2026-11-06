// std::string through the native models.
#include <string>

int t_str_basic(int n) {
  std::string s = "hello";
  s.push_back('!');
  return (int)s.size() * 1000 + s[1] + n;
}

int t_str_append(int n) {
  std::string a = "ab";
  std::string b = "cd";
  a += b;
  a.append("ef");
  a += "g";
  int sum = 0;
  for (char c : a) sum += c - 'a';
  return sum * 100 + (int)a.length() + n;
}

int t_str_compare(int n) {
  std::string a = "abc";
  std::string b = "abc";
  std::string c = "abd";
  int r = 0;
  if (a == b) r += 1;
  if (a == c) r += 10;
  if (n > 0) b.push_back('x');
  if (a == b) r += 100;
  return r;
}

int t_str_copy(int n) {
  std::string a = "xyz";
  std::string b = a;
  b[0] = 'q';
  std::string c(std::move(b));
  return a[0] * 10000 + c[0] * 10 + n + (int)c.size();
}

int t_str_cstr(int n) {
  std::string s = "rst";
  const char *p = s.c_str();
  int r = 0;
  for (int i = 0; p[i] != 0; ++i) r = r * 3 + p[i];
  return r + n;
}
