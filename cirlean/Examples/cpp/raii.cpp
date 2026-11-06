// RAII: destructors run on every exit of a scope (normal exit, return, break, continue).
struct Counter {
  int *count;
  explicit Counter(int *c) : count(c) { ++*count; }
  ~Counter() { --*count; }
};

// While `c` is alive the count is one higher; every exit restores it.
int raii_scope(int *live, int x) {
  Counter c(live);
  if (x < 0) return -1;
  return *live;
}

// A guard per iteration; `break` and `continue` leave its scope early.
int raii_loop(int *live, int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) {
    Counter c(live);
    if (i == 5) break;
    if (i % 2 == 1) continue;
    s += *live;
  }
  return s;
}
