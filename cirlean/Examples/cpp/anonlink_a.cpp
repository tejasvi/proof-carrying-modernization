// Linking units with anonymous records (cir2lean --link, Examples/LinkAnon.lean): clang numbers
// anonymous records per translation unit, so this unit's and anonlink_b.cpp's anonymous unions get
// the same numbers with different layouts, while std::string's union is one type in both units.
#include <string>

struct A1 {
  int tag;
  union {
    int i;
    float f;
  };
};

int b_value(int x);

int a_value(int x) {
  A1 a;
  a.tag = 1;
  a.i = x;
  std::string s = "hello";
  return a.i + (int)s.size() + b_value(x);
}
