// Demo (b2), version after the PR: a result variable and `break` (single exit).
int find_first(int n, int k) {
  int r = -1;
  for (int i = 0; i < n; ++i) {
    if (i * i >= k) {
      r = i;
      break;
    }
  }
  return r;
}
