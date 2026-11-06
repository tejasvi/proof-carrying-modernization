// Loops, break/continue, switch.
int t_for_break_continue(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) {
    if (i % 3 == 0) continue;
    if (i > 20) break;
    s += i;
  }
  return s;
}

int t_while_do(int n) {
  int a = 0, k = n;
  while (k > 0) { a += k; k -= 2; }
  int b = 0;
  do { b += 3; } while (b < n);
  return a * 10 + b;
}

int t_nested_loops(int n) {
  int c = 0;
  for (int i = 0; i < n; ++i)
    for (int j = 0; j < i; ++j) {
      if (j == 2) continue;
      if (i * j > 12) break;
      c += i - j;
    }
  return c;
}

int t_switch_fall(int x) {
  int r = 0;
  switch (x) {
    case 1: r += 1;
    case 2: r += 10; break;
    case 3:
    case 4: r += 100; break;
    case 7: r += 1000;
    default: r += 5;
  }
  return r;
}

int t_switch_loop(int n) {
  int r = 0;
  for (int i = 0; i < n; ++i) {
    switch (i % 4) {
      case 0: r += 1; break;
      case 1: continue;
      case 2: r += 2;
      default: r *= 2;
    }
    r += 1;
  }
  return r;
}

int t_early_return(int a) {
  for (int i = 0; i < 100; ++i) {
    if (i * i > a) return i;
  }
  return -1;
}

static int fib(int n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
int t_recursion(int n) { return fib(n); }
