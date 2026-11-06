// Exceptions: a library function that throws, a handler that catches by type,
// and RAII cleanup on the exceptional path.
#include <cstddef>
#include <stdexcept>
#include <vector>

// v.at(i) throws std::out_of_range for a bad index.
int safe_get(const std::vector<int> &v, std::size_t i) {
  try {
    return v.at(i);
  } catch (const std::out_of_range &) {
    return -1;
  }
}

struct Guard {
  int *count;
  explicit Guard(int *c) : count(c) { ++*count; }
  ~Guard() { --*count; }
};

// The guard's destructor runs when the exception leaves the inner scope.
int guarded_get(int *live, const std::vector<int> &v, std::size_t i) {
  try {
    Guard g(live);
    return v.at(i) + *live;
  } catch (const std::out_of_range &) {
    return *live;
  }
}
