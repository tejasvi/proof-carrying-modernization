// rand / srand (run with CASES=rand_cases.txt): glibc's generator (random_r,
// TYPE_3), so the values are the native ones: without srand the state is
// srand(1)'s, srand(0) seeds as srand(1), seeds above 2^31 - 1 go through
// glibc's 32-bit arithmetic, RAND_MAX is 2^31 - 1. Expected result (labelled
// per case in the cases file): MATCH everywhere.
#include <cstdlib>

int t_rand_nth(int n) {
  int x = 0;
  for (int i = 0; i <= n; ++i) x = rand();
  return x;
}

int t_srand(int n) {
  srand((unsigned)n);
  return rand();
}

int t_srand_nth(int n) {
  srand(12345u);
  int x = 0;
  for (int i = 0; i <= n; ++i) x = rand();
  return x;
}

int t_srand_big(int n) {
  srand(4000000000u + (unsigned)n);
  return rand();
}

int t_rand_sum(int n) {
  srand((unsigned)n);
  long long s = 0;
  for (int i = 0; i < 1000; ++i) s += rand() % 1000;
  return (int)s;
}

int t_rand_max(int) {
  return RAND_MAX;
}

int t_srand_reseed(int n) {
  srand(7u);
  int a = rand();
  (void)rand();
  srand(7u);
  int b = rand();
  return a == b ? n : -1;
}
