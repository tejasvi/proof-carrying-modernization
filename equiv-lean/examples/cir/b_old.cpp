// Demo (b), version before the PR: counting `for` loop.
int sum_below(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) s += i;
  return s;
}
