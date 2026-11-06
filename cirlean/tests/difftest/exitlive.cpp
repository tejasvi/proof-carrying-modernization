// The exit sequence and automatic objects (run with MODE=status
// CASES=exitlive_cases.txt). exit ends the lifetime of no automatic object
// (C11 7.22.4.4; C++: exit destroys none), so the atexit handlers run while the
// objects of the calls in progress are alive; a handler registered during the
// exit sequence runs too, before the earlier ones still to run (C11
// 7.22.4.4p3, as glibc does). The handlers report through _Exit(status).
// Expected result, labelled per case in the cases file: MATCH, or UB from
// cirrun where a handler uses an object whose lifetime has ended.
#include <cstdlib>

static int *g_loc;
static int g_dtors;
static int g_trace;

struct D {
  int *c;
  ~D() { ++*c; }
};

static void h_read_local() { _Exit(*g_loc); }

// a handler reading an automatic object of the function that called exit
int t_auto_in_handler(int) {
  int x = 42;
  g_loc = &x;
  atexit(h_read_local);
  exit(0);
}

// a handler reading an automatic object of a caller several frames up
static void deep(int depth) {
  if (depth == 0) exit(0);
  deep(depth - 1);
}
int t_caller_auto_in_handler(int) {
  int x = 43;
  g_loc = &x;
  atexit(h_read_local);
  deep(3);
  return 0;
}

// a handler writing an automatic object of the function that called exit
static void h_write_local() {
  *g_loc = 5;
  _Exit(*g_loc + 1);
}
int t_handler_writes_local(int) {
  int x = 1;
  g_loc = &x;
  atexit(h_write_local);
  exit(0);
}

// a handler registered by a handler
static void h2() { _Exit(5); }
static void h1() { atexit(h2); }
int t_register_during(int) {
  atexit(h1);
  return 0;
}

// hb runs first and registers hc, which runs before ha: 2, 3, 1
static void ha() {
  g_trace = g_trace * 10 + 1;
  _Exit(g_trace);
}
static void hc() { g_trace = g_trace * 10 + 3; }
static void hb() {
  g_trace = g_trace * 10 + 2;
  atexit(hc);
}
int t_order_during(int) {
  g_trace = 0;
  atexit(ha);
  atexit(hb);
  return 0;
}

// control: an automatic object of a function that has returned
int t_returned_local(int) {
  int x = 44;
  g_loc = &x;
  atexit(h_read_local);
  return 0;
}

// control: an automatic object of a call that returned before exit
static void reg() {
  int y = 9;
  g_loc = &y;
}
int t_after_returned_call(int) {
  reg();
  atexit(h_read_local);
  exit(0);
}

// control: exit inside a loop and a try block: the earlier iterations destroyed
// their objects (2 each), the exiting one destroys none and no handler catches
static void h_count() { _Exit(g_dtors); }
int t_in_loop_try(int) {
  g_dtors = 0;
  atexit(h_count);
  for (int i = 0; i < 5; ++i) {
    D d{&g_dtors};
    try {
      D e{&g_dtors};
      if (i == 2) exit(0);
    } catch (...) {
      g_dtors += 100;
    }
  }
  return 0;
}

// control: exit destroys no automatic object of the calls in progress
static void nested(int depth) {
  D d{&g_dtors};
  if (depth == 0) exit(0);
  nested(depth - 1);
}
int t_no_auto_dtors(int) {
  g_dtors = 0;
  atexit(h_count);
  D d{&g_dtors};
  nested(3);
  return 0;
}
