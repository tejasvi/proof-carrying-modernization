// libc++'s hashing support (run with CASES=gaps3_cases.txt): std::__hash_memory, which libc++'s
// std::hash of string views and strings and __gnu_cxx::hash<const char *> call (CityHash64), and
// std::__next_prime, the bucket counts of the unordered containers. The native side uses libstdc++,
// whose hash functions differ, so the t_ cases use the containers in ways that do not depend on the
// hash values (counts, lookups, sums); v_hash_values returns libc++'s values. Expected result
// (labelled per case in the cases file): MATCH; MISMATCH on v_hash_values; UB from cirrun on
// u_hash_uninit (indeterminate bytes hashed) and on the gap g_hash_string (the characters of a
// std::string are not read).
#include <cstdio>
#include <cstring>
#include <ext/hash_map>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

struct eqstr {
  bool operator()(const char *a, const char *b) const { return strcmp(a, b) == 0; }
};

// as Shootout's hash.cpp: hexadecimal keys from strdup, then the decimal ones looked up
int t_hash_map_count(int k) {
  __gnu_cxx::hash_map<const char *, int, __gnu_cxx::hash<const char *>, eqstr> x;
  int n = 200 + k;
  char buf[16];
  for (int i = 1; i <= n; i++) {
    snprintf(buf, sizeof buf, "%x", i);
    x[strdup(buf)] = i;
  }
  int c = 0;
  for (int i = n; i > 0; i--) {
    snprintf(buf, sizeof buf, "%d", i);
    if (x.find(buf) != x.end())
      c++;
  }
  return c * 1000 + (int) x.size();
}

int t_unordered_int(int k) {
  std::unordered_map<int, int> m;
  for (int i = 0; i < 100; ++i)
    m[i * 7 + k] = i;
  int s = 0;
  for (int i = 0; i < 100; ++i)
    s += m.count(i) ? m[i] : 0;
  return s * 1000 + (int) m.size();
}

int t_string_view_set(int k) {
  const char text[] = "the quick brown fox jumps over the lazy dog the fox";
  std::unordered_set<std::string_view> words;
  const char *p = text;
  while (*p) {
    const char *q = p;
    while (*q && *q != ' ')
      ++q;
    words.insert(std::string_view(p, q - p));
    p = *q ? q + 1 : q;
  }
  return (int) words.size() + k + (words.count("fox") ? 100 : 0);
}

// libc++'s hashes of strings of 0 to 80 bytes (each length range of CityHash64)
int v_hash_values(int k) {
  char s[96];
  for (int i = 0; i < 96; ++i)
    s[i] = (char) ('a' + (i * 7 + k) % 26);
  const int lens[] = {0, 3, 7, 12, 20, 40, 80};
  unsigned long h = 0;
  for (int n : lens)
    h = h * 31 + std::hash<std::string_view>{}(std::string_view(s, n));
  return (int) (h % 1000003);
}

// undefined: the bytes hashed are indeterminate
int u_hash_uninit(int k) {
  char buf[8];
  return (int) (std::hash<std::string_view>{}(std::string_view(buf, 4)) & 1) + k;
}

// gap: the characters of a std::string are not read
int g_hash_string(int k) {
  std::unordered_set<std::string> s;
  s.insert("abc");
  s.insert("abd");
  s.insert("abc");
  return (int) s.size() + k;
}
