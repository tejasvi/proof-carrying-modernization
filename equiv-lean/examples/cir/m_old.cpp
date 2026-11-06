// Demo (b4), version before the PR: two `for` loops in sequence.
int sum_then_count(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) s += i;
  int c = 0;
  for (int j = 0; j < s; ++j) c += 1;
  return c;
}
