// Test functions with concrete inputs: their theorems are proved by
// evaluation from the program's initial memory (`cir_init_mem; cir_eval`),
// with no loop invariant.
#include <cstring>

static int count_chars(const char *s, char c) {
  int n = 0;
  for (int i = 0; s[i]; ++i)
    if (s[i] == c)
      ++n;
  return n;
}

int test_loop() {
  int s = 0;
  for (int i = 0; i < 10; ++i)
    s += i;
  return s;
}

int test_count() { return count_chars("hello world", 'o') == 2 ? 0 : 1; }

int test_strlen() { return (int)strlen("abcdef"); }
