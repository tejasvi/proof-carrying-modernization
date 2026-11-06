// exit called in main keeps main's automatic objects alive for the exit
// sequence (C11 7.22.4.4), unlike a return from main (exitlive_main.cpp); run
// with MODE=status CASES=exitlive_cases.txt. Expected result: MATCH, status 7.
#include <cstdlib>

static int *g_loc;
static void h() { _Exit(*g_loc); }

int main() {
  int x = 7;
  g_loc = &x;
  atexit(h);
  exit(0);
}
