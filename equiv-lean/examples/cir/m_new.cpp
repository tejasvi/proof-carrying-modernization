// Demo (b4), version after the PR: the first loop as a `while`, increments rewritten.
int sum_then_count(int n) {
  int s = 0;
  int i = 0;
  while (i < n) {
    s = s + i;
    i++;
  }
  int c = 0;
  for (int j = 0; j < s; j++) c++;
  return c;
}
