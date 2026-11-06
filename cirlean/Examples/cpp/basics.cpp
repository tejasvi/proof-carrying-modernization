// Small functions used to exercise the verification pipeline.
int add3(int a) { return a + 3; }

int max2(int a, int b) { return a > b ? a : b; }

int abs_val(int x) {
  if (x < 0) return -x;
  return x;
}

int sum_to(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) s += i;
  return s;
}

void swap_ints(int *a, int *b) {
  int t = *a;
  *a = *b;
  *b = t;
}

struct Point { int x, y; };

int manhattan(const Point &p) {
  return (p.x < 0 ? -p.x : p.x) + (p.y < 0 ? -p.y : p.y);
}

int count_up(int n) {
  int c = 0;
  for (int i = 0; i < n; ++i) c += 2;
  return c;
}

int countdown(int n) {
  int steps = 0;
  while (n > 0) {
    n = n - 1;
    steps = steps + 1;
  }
  return steps;
}
