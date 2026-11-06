// exit(3) from main after output. The static object's destructor runs in the
// exit sequence, as after a return from main (return_main.cpp).
#include <cstdio>
#include <cstdlib>

struct Noisy {
  ~Noisy() { printf("~Noisy (static)\n"); }
};

Noisy noisy;

int main() {
  printf("main\n");
  exit(3);
}
