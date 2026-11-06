// Demo (b3), version after the PR: range-for.
#include <vector>

int vsum(const std::vector<int> &v) {
  int s = 0;
  for (int x : v) s += x;
  return s;
}
