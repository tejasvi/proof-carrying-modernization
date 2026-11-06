// The exit sequence (MODE=status CASES=exit_cases.txt): exit runs the atexit handlers, the last
// registered first, then the destructors of static objects, as a return from main does; _Exit
// and quick_exit run neither. The handlers and destructors that run append a digit to `code`,
// and the last one ends the program with `_Exit(code)` (allowed during the exit sequence), so
// the status tells which ran, in which order.
#include <cstdio>
#include <cstdlib>

static int code = 0;
static int armed = 0;
static void note(int d) { code = code * 10 + d; }
static void h_end() { _Exit(code); }
static void h_1() { note(1); }
static void h_2() { note(2); }
static void h_exit() { exit(9); }

// prints when destroyed; once armed, r5 (constructed first, destroyed last) ends the program
struct Reporter {
  int d;
  ~Reporter() {
    printf("~Reporter %d\n", d);
    if (armed) {
      note(d);
      if (d == 5) _Exit(code);
    }
  }
};
Reporter r5{5};
Reporter r4{4};

// exit after atexit(h_end), atexit(h_2), atexit(h_1): h_1, h_2, h_end run: status 12
int t_exit_handlers(int n) {
  atexit(h_end);
  atexit(h_2);
  atexit(h_1);
  exit(n);
}

// a return from main runs the same sequence: 12
int t_return_handlers(int n) {
  atexit(h_end);
  atexit(h_2);
  atexit(h_1);
  return n;
}

// exit reaches the static objects' destructors (they print): r4, then r5, which ends with 45
int t_exit_statics(int n) {
  armed = 1;
  exit(n);
}

// a handler registered after the static objects were constructed runs before their
// destructors: h_1, r4, r5: 145
int t_exit_handler_statics(int n) {
  armed = 1;
  atexit(h_1);
  exit(n);
}

// _Exit runs no handler and no static destructor: the status is n
int t_Exit_skips(int n) {
  armed = 1;
  atexit(h_1);
  atexit(h_end);
  _Exit(n);
}

// quick_exit neither (no at_quick_exit handler is registered): n
int t_quick_exit_skips(int n) {
  armed = 1;
  atexit(h_1);
  atexit(h_end);
  quick_exit(n);
}

// exit from an atexit handler, during the exit sequence: undefined (C11 7.22.4.4p2)
int t_exit_in_handler(int n) {
  atexit(h_exit);
  exit(n);
}
