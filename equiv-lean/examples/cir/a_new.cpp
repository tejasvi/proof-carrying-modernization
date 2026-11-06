// Demo (a), version after the PR: std::min / std::max.
#include <algorithm>

int clamp(int x, int lo, int hi) {
  return x < lo ? lo : std::min(x, hi);
}

int max3(int a, int b, int c) {
  return std::max(a, std::max(b, c));
}
