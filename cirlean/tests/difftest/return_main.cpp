// A return from main: the status is the returned value. The static object's
// destructor runs after main returns, in the exit sequence.
#include <cstdio>

struct Noisy {
  ~Noisy() { printf("~Noisy (static)\n"); }
};

Noisy noisy;

int main() {
  printf("main\n");
  return 7;
}
