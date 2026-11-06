// exit(3) from a constructor, before main: the exit sequence runs for what was constructed
// before it, so `first`'s destructor ends the program with status 42; main never runs.
#include <cstdio>
#include <cstdlib>

static int code = 0;

struct First {
  ~First() {
    printf("~First\n");
    _Exit(code + 40);
  }
};
First first;

struct Quitter {
  Quitter() {
    code = 2;
    exit(3);
  }
};
Quitter quitter;

int main() {
  printf("main\n");
  return 7;
}
