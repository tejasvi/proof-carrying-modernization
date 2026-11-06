/* Two loops in one function: the second loop's variables were last written
   before the first loop (or in a scope that the first loop's block closes). */
int fill_after_count(int *a, int n) {
  int *p = a;
  int count = 0;
  {
    int i = 0;
    while (i < n) {
      count++;
      i++;
    }
  }
  int j = 0;
  while (j < count) {
    p[j] = 7;
    j++;
  }
  return count;
}
