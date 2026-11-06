// Program termination (MODE=status CASES=exit_cases.txt): exit, _Exit and
// quick_exit end the program with their status, as a return of it from main
// would (C11 5.1.2.2.3, 7.22.4.4). exit destroys no automatic object and is
// not an exception. A Sentry's destructor would change the status if it ran
// after exit (it calls exit itself once `exiting` is set).
#include <cstdio>
#include <cstdlib>

static int exiting = 0;

struct Sentry {
  int code;
  Sentry(int c) : code(c) {}
  ~Sentry() {
    printf("~Sentry %d\n", code);
    if (exiting) exit(code);
  }
};

// ends the program from its destructor, at the end of its scope
struct Closer {
  int code;
  Closer(int c) : code(c) {}
  ~Closer() { exit(code); }
};

static void leave(int n) {
  exiting = 1;
  exit(n);
}

static int depth2(int n) {
  if (n > 0) leave(n);
  return 40;
}

static int depth1(int n) {
  Sentry s(8);
  return depth2(n) + 1;
}

int t_exit_direct(int n) { exit(n); }

int t_exit_nested(int n) {
  Sentry s(9);
  return depth1(n) + 1;
}

int t_exit_for(int n) {
  int acc = 0;
  for (int i = 0; i < 10; ++i) {
    Sentry s(20 + i);
    acc += i;
    if (i == n) leave(acc + 30);
  }
  return acc;
}

static int check(int i, int n) {
  if (i == n) leave(10 + i);
  return i < 5;
}

int t_exit_while_cond(int n) {
  int i = 0;
  while (check(i, n)) ++i;
  return 50 + i;
}

int t_exit_do_cond(int n) {
  int i = 0;
  do { ++i; } while (check(i, n));
  return 60 + i;
}

int t_exit_after_printf(int n) {
  printf("before exit %d\n", n);
  exit(n);
}

int t_exit_auto_dtor(int n) {
  Sentry s(9);
  if (n > 0) leave(n);
  return 0;
}

int t_exit_in_try(int n) {
  try {
    Sentry s(9);
    depth1(n);
  } catch (...) {
    return 77;
  }
  return 66;
}

int t_exit_switch(int n) {
  switch (n) {
  case 1:
    exit(11);
  case 2: {
    Sentry s(9);
    leave(12);
  }
  default:
    break;
  }
  return 13;
}

int t_exit_from_dtor(int n) {
  {
    Closer c(n);
  }
  return 99;
}

int t_exit_fnptr(int n) {
  void (*quit)(int) = exit;
  Sentry s(9);
  exiting = 1;
  quit(n);
  return 98;
}

int t_Exit(int n) {
  Sentry s(9);
  exiting = 1;
  _Exit(n);
}

int t_quick_exit(int n) {
  Sentry s(9);
  exiting = 1;
  quick_exit(n);
}

int t_exit_wide(int n) { exit(256 + n); }

int t_exit_neg(int n) { exit(-n); }

int t_return_plain(int n) {
  Sentry s(9);
  return 2 * n;
}
