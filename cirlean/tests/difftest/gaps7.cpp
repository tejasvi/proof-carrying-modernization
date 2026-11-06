// Stores of empty values (run with CASES=gaps7_cases.txt): CIR's records leave out an empty member
// ([[no_unique_address]], as in libc++'s compressed pairs), and CIR stores such a member's value through
// a cast of the address it shares with another member. An empty class has no value representation
// ([intro.object]p9), so in a C++ module those stores and copies write nothing (the frontend drops them).
// libc++'s map, set and list copy constructors build their allocators that way. Expected result
// (labelled per case in the cases file): MATCH.
#include <list>
#include <map>
#include <set>
#include <vector>

struct Empty {};
static Empty make() { return Empty(); }

// the empty member built after the pointer it overlaps
struct Pair {
  int *p;
  [[no_unique_address]] Empty e;
  Pair(int *q) : p(q), e(make()) {}
};
int t_nua_after(int k) {
  int x = 5 + k;
  Pair q(&x);
  return *q.p;
}

// the empty member built before the pointer
struct Pair2 {
  [[no_unique_address]] Empty e;
  int *p;
  Pair2(int *q) : e(make()), p(q) {}
};
int t_nua_before(int k) {
  int x = 7 + k;
  Pair2 q(&x);
  return *q.p;
}

// an empty member assigned after the pointer it overlaps
int t_nua_assign(int k) {
  int x = 9 + k;
  Pair q(&x);
  Empty other;
  q.e = other;
  return *q.p;
}

int t_map_copy(int k) {
  std::map<unsigned, std::vector<unsigned>> m;
  for (unsigned i = 0; i < 5; ++i)
    m[i] = std::vector<unsigned>(i + 1, i + k);
  std::map<unsigned, std::vector<unsigned>> c(m);
  unsigned s = 0;
  for (auto &kv : c)
    for (unsigned v : kv.second)
      s += v;
  return (int) (s * 10 + c.size());
}

int t_map_assign(int k) {
  std::map<int, int> m;
  for (int i = 0; i < 6; ++i)
    m[i] = i * i + k;
  std::map<int, int> c;
  c[100] = 1;
  c = m;
  int s = 0;
  for (auto &kv : c)
    s += kv.second;
  return s * 10 + (int) c.size();
}

int t_set_copy(int k) {
  std::set<int> s;
  for (int i = 0; i < 8; ++i)
    s.insert((i * 7 + k) % 10);
  std::set<int> c = s;
  int t = 0;
  for (int v : c)
    t = t * 3 + v;
  return t;
}

int t_list_copy(int k) {
  std::list<int> l;
  for (int i = 0; i < 6; ++i)
    l.push_back(i + k);
  std::list<int> c(l);
  int t = 0;
  for (int v : c)
    t = t * 5 + v;
  return t + (int) c.size();
}
