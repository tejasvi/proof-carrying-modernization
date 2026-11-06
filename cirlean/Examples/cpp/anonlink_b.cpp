// The other unit of Examples/LinkAnon.lean: another anonymous union (a different layout) and
// std::string.
#include <string>

struct B1 {
  union {
    long l;
    double d;
  };
  char c;
};

int b_value(int x) {
  B1 b;
  b.l = 2L * x;
  b.c = 'z';
  std::string t = "ab";
  return (int)b.l + (int)t.size() + (b.c == 'z');
}
