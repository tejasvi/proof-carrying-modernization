// Demo (b), version after the PR: the same loop as a `while`.
int sum_below(int n) {
  int s = 0;
  int i = 0;
  while (i < n) {
    s = s + i;
    i++;
  }
  return s;
}
