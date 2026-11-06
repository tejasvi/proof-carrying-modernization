// C-style arrays: pointer arithmetic with a variable offset, and a forward
// goto out of a loop (the C idiom for early exits).
int sum_arr(const int *a, int n) {
  int s = 0;
  for (int i = 0; i < n; ++i)
    s += a[i];
  return s;
}

int find_first(const int *a, int n, int key) {
  int i;
  for (i = 0; i < n; ++i)
    if (a[i] == key)
      goto found;
  return -1;
found:
  return i;
}
