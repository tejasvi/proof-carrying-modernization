// std::optional, std::unique_ptr, std::min/max/swap.
#include <optional>
#include <memory>
#include <algorithm>
#include <utility>

static std::optional<int> half(int x) {
  if (x % 2 == 0) return x / 2;
  return std::nullopt;
}

int t_opt(int x) {
  std::optional<int> h = half(x);
  int r = 0;
  if (h.has_value()) r += *h * 10;
  if (!h) r -= 1;
  r += h.value_or(1000);
  return r;
}

int t_opt_value_throw(int x) {
  std::optional<int> h = half(x);
  try {
    return h.value();
  } catch (...) {
    return -7;
  }
}

int t_uptr(int x) {
  std::unique_ptr<int> p(new int(x));
  std::unique_ptr<int> q = std::move(p);
  int r = 0;
  if (!p) r += 1;
  if (q) r += *q * 10;
  q.reset(new int(x + 1));
  r += *q.get() * 100;
  return r;
}

int t_minmax_swap(int a, int b) {
  int lo = std::min(a, b);
  int hi = std::max(a, b);
  int x = a, y = b;
  std::swap(x, y);
  return lo * 1000000 + hi * 1000 + (x - y);
}
