/* Loops that write arrays: a local array, a static global, a function-local
   static (cir_loop names an array's elements; Examples/ArrLoop.lean). */
int fill_local(int n) {
  int a[8];
  for (int i = 0; i < 8; i++) a[i] = n;
  return a[3];
}

static int table[16];
int fill_static(int k) {
  for (int i = 0; i < 16; i++) table[i] = k;
  return table[15];
}

int bump_all(int n) {
  static int counts[4];
  for (int i = 0; i < n; i++) counts[i % 4] += 1;
  return counts[0];
}
