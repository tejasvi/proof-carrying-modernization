// Demo (b2), version before the PR: early `return` from inside the loop.
int find_first(int n, int k) {
  for (int i = 0; i < n; ++i)
    if (i * i >= k) return i;
  return -1;
}
