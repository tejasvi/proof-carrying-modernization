// Loop bound, after: `!=` test (equivalent for n >= 0).
int twice(int n) {
  int s = 0;
  for (int i = 0; i != n; ++i) s += 2;
  return s;
}
