// std::vector examples for the verification pipeline (compiled against libc++).
#include <cstddef>
#include <optional>
#include <vector>

int vsum(const std::vector<int> &v) {
  int s = 0;
  for (std::size_t i = 0; i < v.size(); ++i) s += v[i];
  return s;
}

int vsum_range(const std::vector<int> &v) {
  int s = 0;
  for (int x : v) s += x;
  return s;
}

int count_eq(const std::vector<int> &v, int key) {
  int c = 0;
  for (std::size_t i = 0; i < v.size(); ++i)
    if (v[i] == key) ++c;
  return c;
}

void fill_iota(std::vector<int> &out, int n) {
  out.clear();
  for (int i = 0; i < n; ++i) out.push_back(i);
}

std::optional<int> find_index(const std::vector<int> &v, int key) {
  for (std::size_t i = 0; i < v.size(); ++i)
    if (v[i] == key) return static_cast<int>(i);
  return std::nullopt;
}
