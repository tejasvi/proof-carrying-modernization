// Modular verification: callers are verified against the specifications of
// their callees, not their bodies.
int twice(int x) { return x + x; }

int quad(int x) { return twice(twice(x)); }

// A callee with a loop: its callers need no loop invariant.
int count_to(int n) {
  int c = 0;
  for (int i = 0; i < n; ++i)
    c += 1;
  return c;
}

int count_plus_one(int n) { return count_to(n) + 1; }

// A callee that writes through a pointer into the caller's frame.
void incr(int *p) { *p = *p + 1; }

int incr_twice(int x) {
  int y = x;
  incr(&y);
  incr(&y);
  return y;
}
