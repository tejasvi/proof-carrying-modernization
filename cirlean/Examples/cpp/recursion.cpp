// Recursion and mutual recursion: specifications proved by induction, with
// the induction hypothesis as the callee's contract.
int fact(int n) { return n <= 1 ? 1 : n * fact(n - 1); }

int sum_down(int n) {
  if (n <= 0)
    return 0;
  return n + sum_down(n - 1);
}

bool is_odd(unsigned n);
bool is_even(unsigned n) { return n == 0 ? true : is_odd(n - 1); }
bool is_odd(unsigned n) { return n == 0 ? false : is_even(n - 1); }
