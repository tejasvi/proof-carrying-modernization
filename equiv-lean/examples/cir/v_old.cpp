// Demo (b3), version before the PR: index loop over a std::vector.
#include <vector>

int vsum(const std::vector<int> &v) {
  int s = 0;
  for (std::size_t i = 0; i < v.size(); ++i) s += v[i];
  return s;
}
