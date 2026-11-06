// A return from main ends the lifetime of main's automatic objects before the
// exit sequence (C++ [basic.start.main]; C11 6.2.4p2), so a handler reading one
// is undefined (run with MODE=status CASES=exitlive_cases.txt). Expected result:
// UB from cirrun.
#include <cstdlib>

static int *g_loc;
static void h() { _Exit(*g_loc); }

int main() {
  int x = 7;
  g_loc = &x;
  atexit(h);
  return 0;
}
