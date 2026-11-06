// exit(0) from main with an automatic object: exit does not destroy it, so its
// destructor's output does not appear natively.
#include <cstdio>
#include <cstdlib>

struct Loud {
  ~Loud() { printf("~Loud (automatic)\n"); }
};

int main() {
  Loud l;
  printf("main\n");
  exit(0);
}
