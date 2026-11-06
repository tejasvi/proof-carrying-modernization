// setjmp / longjmp (CASES=sjlj_cases.txt). A longjmp returns to its setjmp, which returns again
// with the value given (1 for 0, C11 7.13.2.1p4). setjmp may only be the whole controlling
// expression of a selection or iteration statement (also compared with an integer constant, or
// under !) or an expression statement (7.13.1.1p4); the automatic objects that are not volatile
// and changed between setjmp and longjmp are indeterminate afterwards (7.13.2.1p3); longjmp to a
// setjmp whose function has returned is undefined (7.13.2.1p2), and in C++ so is one that skips
// a non-trivial destructor ([csetjmp.syn]p2). The cases labelled UB break those rules (natively
// they do something); the gaps are cirlean's.
#include <csetjmp>
#include <setjmp.h>

static volatile int trail;

// longjmp three frames down, through frames with their own setjmp and jmp_buf
static void far3(std::jmp_buf b, int k) {
  trail = trail * 10 + 3;
  std::longjmp(b, k);
}
static void far2(std::jmp_buf b, int k) {
  std::jmp_buf mine;
  trail = trail * 10 + 2;
  if (!setjmp(mine)) far3(b, k);
  trail = 900;
}
static void far1(std::jmp_buf b, int k) {
  std::jmp_buf mine;
  trail = trail * 10 + 1;
  if (!setjmp(mine)) far2(b, k);
  trail = 800;
}
int t_far(int k) {
  std::jmp_buf b;
  trail = 0;
  switch (setjmp(b)) {
  case 0: far1(b, k); return -1;
  case 5: return trail * 10 + 5;
  default: return trail * 10;
  }
}

// repeated jumps to one setjmp, counted in a volatile object
int t_loop(int n) {
  std::jmp_buf b;
  volatile int i = 0;
  if (setjmp(b) < 4) {
    ++i;
    std::longjmp(b, i + n);
  }
  return i * 100 + n;
}

// a global jmp_buf; the longjmp comes from a later statement's callee
static std::jmp_buf gbuf;
static void thrower() { std::longjmp(gbuf, 1); }
static void catcher(int *x, int k) {
  if (setjmp(gbuf)) return;
  *x = k;
  thrower();
  *x = -1;
}
int t_inline(int k) {
  int a = 1;
  catcher(&a, k);
  return a;
}

// longjmp(b, 0) makes setjmp return 1
int t_zero(int k) {
  std::jmp_buf b;
  volatile int seen = 0;
  switch (setjmp(b)) {
  case 0: seen = 1; std::longjmp(b, 0);
  case 1: return seen * 10 + 1 + k;
  default: return -1;
  }
}

// a volatile object changed before the longjmp keeps its new value, an unchanged one its value
int t_kept(int k) {
  std::jmp_buf b;
  volatile int v = 1;
  int same = k;
  if (setjmp(b) == 0) {
    v = 2;
    std::longjmp(b, 1);
  }
  return v * 100 + same;
}

// setjmp as an expression statement, jumped back to from a later statement
int t_stmt(int n) {
  std::jmp_buf b;
  static int k;
  k = 0;
  setjmp(b);
  if (++k < n) std::longjmp(b, 1);
  return k;
}

// a second setjmp on the same buffer: the longjmp goes to the latest
static volatile int ms;
static void jump(std::jmp_buf b, int v) { std::longjmp(b, v); }
int t_multiple(int k) {
  std::jmp_buf b;
  ms = 0;
  if (setjmp(b) != 0) {
    ms = ms * 10 + 1;
    if (setjmp(b) != 0) {
      ms = ms * 10 + 2;
      return ms + k;
    }
    jump(b, 2);
  }
  jump(b, 1);
  return -1;
}

// the statements after the setjmp's statement and enclosing block run again
int t_after_block(int k) {
  std::jmp_buf b;
  volatile int pass = 0;
  {
    if (setjmp(b) != 0) return 100 + pass + k;
  }
  if (pass++ == 0) std::longjmp(b, 1);
  return -1;
}

// sigsetjmp / siglongjmp
int t_sig(int k) {
  sigjmp_buf b;
  if (sigsetjmp(b, 1) == 0) siglongjmp(b, k + 1);
  return k * 2;
}

// UB: a non-volatile object changed between setjmp and longjmp, then read (7.13.2.1p3)
int t_ub_changed(int k) {
  std::jmp_buf b;
  int x = 1;
  if (setjmp(b) == 0) {
    x = k;
    std::longjmp(b, 1);
  }
  return x;
}

// UB: setjmp in an assignment and in an initializer (7.13.1.1p4-5)
int t_ub_assign(int k) {
  std::jmp_buf b;
  volatile int r;
  if ((r = setjmp(b)) != 0) return r + k;
  std::longjmp(b, 5);
}
int t_ub_init(int k) {
  std::jmp_buf b;
  int r = setjmp(b);
  if (r == 0) std::longjmp(b, k + 1);
  return r;
}

// UB: a longjmp over a non-trivial destructor ([csetjmp.syn]p2)
struct Bump {
  int *p;
  ~Bump() { ++*p; }
};
static std::jmp_buf dbuf;
static void with_dtor(int *p) {
  Bump bump{p};
  std::longjmp(dbuf, 1);
}
int t_ub_dtor(int k) {
  int n = k;
  if (!setjmp(dbuf)) with_dtor(&n);
  return n;
}

// UB: longjmp to a setjmp whose function has returned (7.13.2.1p2)
static std::jmp_buf stale;
static int arm() {
  if (setjmp(stale)) return 1;
  return 0;
}
int t_ub_dead(int k) {
  if (arm() == 0) std::longjmp(stale, k + 1);
  return 2;
}

// a goto out of the setjmp's statement after the longjmp
int t_goto_out(int k) {
  std::jmp_buf b;
  volatile int pass = 0;
  if (setjmp(b) != 0) goto out;
  if (pass++ == 0) std::longjmp(b, 1);
  return -1;
out:
  return 100 + pass + k;
}

// gaps: setjmp in a loop condition jumped back to from the body; a longjmp after the setjmp's
// if branch was left; a longjmp after the setjmp's statement, in a block that branches to a label
int t_gap_loop_cond(int k) {
  std::jmp_buf b;
  volatile int c = 0;
  while (setjmp(b) < 3) {
    if (c++ > 5) break;
    std::longjmp(b, c);
  }
  return c + k;
}
int t_gap_branch_left(int k) {
  std::jmp_buf b;
  volatile int pass = 0;
  if (k > 0) {
    if (setjmp(b) != 0) return 100 + pass;
  }
  if (pass++ == 0) std::longjmp(b, 1);
  return -1;
}
int t_gap_label(int k) {
  std::jmp_buf b;
  volatile int pass = 0;
  if (setjmp(b) != 0) return 100 + pass + k;
again:
  if (pass++ == 0) std::longjmp(b, 1);
  if (pass < 0) goto again;
  return -1;
}
