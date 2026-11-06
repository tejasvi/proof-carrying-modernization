// POSIX threads library models: pthread_self, pthread_equal (one thread; glibc's ids are the
// addresses of the threads' descriptors, so the id itself is not compared, only relations).
#include <pthread.h>

int t_self_equal(int x) {
  pthread_t a = pthread_self();
  pthread_t b = pthread_self();
  return (pthread_equal(a, b) != 0) * 10 + x;
}

int t_self_nonzero(int x) {
  return (pthread_self() != 0) * 10 + x;
}

// glibc compares the values (POSIX leaves an id that is not a thread's undefined)
int t_equal_other(int x) {
  pthread_t a = pthread_self();
  return (pthread_equal(a, a + 1 + (unsigned)x) != 0) * 10 + x;
}
