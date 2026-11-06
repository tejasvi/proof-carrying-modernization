// Program termination: exit ends the program with its status. It is not a
// return, no handler catches it, and it runs no destructor of an automatic
// object.
#include <cstdlib>

// The argument, or exit(2) for a negative one.
int checked(int x) {
  if (x < 0) exit(2);
  return x;
}

struct Guard {
  int *count;
  explicit Guard(int *c) : count(c) { ++*count; }
  ~Guard() { --*count; }
};

// exit(3) inside a try block holding a guard: the handler does not see it and
// the guard's destructor does not run, so *live stays incremented.
int guarded_exit(int *live, int x) {
  try {
    Guard g(live);
    if (x != 0) exit(3);
    return *live;
  } catch (...) {
    return -1;
  }
}
