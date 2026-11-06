// C++ side of the C++ -> Rust collections migration demo (Demo/XLang/VecSum.lean):
// index loop over a std::vector<int> (same function as examples/cir/v_old.cpp).
#include <vector>

int vsum(const std::vector<int> &v) {
  int s = 0;
  for (std::size_t i = 0; i < v.size(); ++i) s += v[i];
  return s;
}
