// std::atomic<int> members (run with CASES=atomics2_cases.txt): exchange,
// compare_exchange_strong and compare_exchange_weak lower to cir.atomic.xchg /
// cir.atomic.cmpxchg (see atomics2.cpp for their meaning). Expected result
// (labelled per case in the cases file): MATCH.
#include <atomic>

struct Ctl {
  std::atomic<int> use;
  std::atomic<int> weak;
};

// exchange, then a compare_exchange_strong that succeeds and a
// compare_exchange_weak that fails unless b is 0 (its expected value is 0)
int s_atomic_members(int a, int b) {
  Ctl c;
  c.use.store(a);
  c.weak.store(b);
  int old = c.use.exchange(b + 1);
  int e = b + 1;
  bool ok1 = c.use.compare_exchange_strong(e, 7);
  int e2 = 0;
  bool ok2 = c.weak.compare_exchange_weak(e2, 9);
  return old * 100000 + ok1 * 10000 + ok2 * 1000 + c.use.load() * 100 + c.weak.load() * 10 + e2;
}

// a counter incremented unless zero with compare_exchange_weak in a loop
int s_inc_unless_zero(int a) {
  std::atomic<int> n(a);
  int cur = n.load(std::memory_order_relaxed);
  do {
    if (cur == 0) return -1;
  } while (!n.compare_exchange_weak(cur, cur + 1, std::memory_order_acq_rel, std::memory_order_relaxed));
  return n.load();
}
