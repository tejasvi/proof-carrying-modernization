// RAII: destructors on every scope exit (cir.cleanup.scope).
struct Log {
  int *acc;
  int digit;
  Log(int *a, int d) : acc(a), digit(d) {}
  ~Log() { *acc = *acc * 10 + digit; }
};

int t_raii_order(int n) {
  int acc = 0;
  {
    Log a(&acc, 1);
    Log b(&acc, 2);
    if (n > 0) { Log c(&acc, 3); }
  }
  return acc;
}

int t_raii_loop_exits(int n) {
  int acc = 0;
  for (int i = 0; i < n; ++i) {
    Log g(&acc, i % 10);
    if (i == 1) continue;
    if (i == 3) break;
  }
  return acc;
}

static int helper_ret(int *acc, int x) {
  Log a(acc, 4);
  if (x > 0) { Log b(acc, 5); return x; }
  Log c(acc, 6);
  return -x;
}

int t_raii_return(int x) {
  int acc = 0;
  int r = helper_ret(&acc, x);
  return acc * 100 + r;
}

struct Counter {
  int *live;
  Counter(int *l) : live(l) { ++*live; }
  Counter(const Counter &o) : live(o.live) { ++*live; }
  ~Counter() { --*live; }
};

int t_raii_copy(int n) {
  int live = 0;
  int peak = 0;
  {
    Counter a(&live);
    Counter b = a;
    for (int i = 0; i < n; ++i) {
      Counter c(&live);
      if (live > peak) peak = live;
    }
  }
  return peak * 10 + live;
}

int t_raii_throw(int x) {
  int acc = 0;
  try {
    Log a(&acc, 7);
    if (x > 2) throw x;
    Log b(&acc, 8);
  } catch (int e) {
    return acc * 100 + e;
  }
  return acc;
}
