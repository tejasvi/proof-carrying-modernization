/* setjmp and longjmp after rog's audit of next3 (CASES=auditsj_cases.txt): the functions s_* to
   z_* up to s_volatile_pointer_after are rog's (soundaudit_n3: n3sjlj.c, n3sj2.c, n3b3.c,
   n3b4.c), the ones after it this branch's. A changed object (C11 7.13.2.1p3) is one stored into
   between the setjmp and the longjmp, the same value or a value restored later included; a
   volatile one is told by its accesses, as CIR types no object volatile. */
#include <setjmp.h>
#include <stdarg.h>
#include <stdio.h>

static jmp_buf env;
static int deep(int n) {
  if (n == 0) longjmp(env, 1);
  return deep(n - 1) + 1;
}
static void jump(void) { longjmp(env, 1); }
static void touch(int *p) { *p = *p + 1; }

/* changed, then changed back to its value at the setjmp: changed between the
   setjmp and the longjmp, so indeterminate (7.13.2.1p3) */
int s_changed_back(int k) {
  int x = 1 + k;
  if (setjmp(env) == 0) {
    x = 2;
    x = 1 + k;
    deep(2);
  }
  return x;
}
/* stored with the value it already had */
int s_stored_same(int k) {
  int x = 1 + k;
  if (setjmp(env) == 0) {
    x = 1 + k;
    deep(2);
  }
  return x;
}
/* changed through a volatile lvalue, but its own type is not volatile-qualified */
int s_volatile_lvalue(int k) {
  int x = 1 + k;
  if (setjmp(env) == 0) {
    *(volatile int *)&x = 5;
    deep(1);
  }
  return x;
}
/* changed by a callee through a pointer */
int s_changed_by_callee(int k) {
  int x = 1 + k;
  if (setjmp(env) == 0) {
    touch(&x);
    deep(1);
  }
  return x;
}
/* unchanged: keeps its value */
int s_unchanged(int k) {
  int x = 7 + k;
  if (setjmp(env) == 0) deep(1);
  return x;
}
/* a volatile object changed: keeps the new value */
int s_volatile_changed(int k) {
  volatile int x = 1 + k;
  if (setjmp(env) == 0) {
    x = 9;
    deep(1);
  }
  return x;
}
/* setjmp in an initializer (7.13.1.1p5) in a function whose body branches (a goto) */
int s_init_goto(int k) {
  int y = setjmp(env);
  if (k) goto out;
  y = y + 1;
out:
  return y + 10;
}
/* a structure with one volatile member: w is not volatile-qualified, changed: indeterminate */
struct VW { volatile int v; int w; };
int s_member_volatile(int k) {
  struct VW s;
  s.v = 1;
  s.w = 2 + k;
  if (setjmp(env) == 0) {
    s.v = 3;
    s.w = 4;
    deep(1);
  }
  return s.w;
}
/* a volatile object that this function only reaches through calls: keeps its new value */
static void setv(volatile int *p, int v) { *p = v; }
static int getv(volatile int *p) { return *p; }
int s_volatile_via_callee(int k) {
  volatile int x;
  setv(&x, 1 + k);
  if (setjmp(env) == 0) {
    setv(&x, 9);
    deep(1);
  }
  return getv(&x);
}
/* a printf-family call after the setjmp, in the same block: %d with a long (7.21.6.1p9) */
int s_fmt_after_setjmp(int k) {
  char buf[32];
  if (setjmp(env) == 0) {
    sprintf(buf, "%d", 1L + k);
  }
  return buf[0];
}
/* flowing off the end after a setjmp, the value discarded by the caller (6.9.1p12: defined) */
static int flow_sj(int k) {
  if (setjmp(env) == 0) {
    if (k) return 5;
  }
}
int s_flowoff_after_setjmp(int k) {
  flow_sj(k);
  return 7;
}
/* a parameter (an automatic object of the function) changed between setjmp and longjmp */
int s_param_changed(int k) {
  if (setjmp(env) == 0) {
    k = k + 5;
    jump();
  }
  return k;
}
/* fprintf to stderr, %d with a long, after a setjmp */
int s_fprintf_after_setjmp(int k) {
  if (setjmp(env) == 0) fprintf(stderr, "%d\n", 1L + k);
  return 2;
}
/* a volatile object reached only through a pointer in its own function, changed after setjmp */
int s_volatile_via_pointer(int k) {
  volatile int x;
  volatile int *p = &x;
  *p = 1 + k;
  if (setjmp(env) == 0) {
    *p = 9;
    jump();
  }
  return *p;
}
/* a volatile object first set by a callee, then changed through a pointer after the setjmp */
int s_volatile_pointer_after(int k) {
  volatile int x;
  volatile int *p = &x;
  setv(p, 1 + k);
  if (setjmp(env) == 0) {
    *p = 9;
    jump();
  }
  return *p;
}

/* --- this branch's */
/* the volatile member of a structure keeps the value it was changed to */
int t_member_volatile_kept(int k) {
  struct VW s;
  s.v = 1;
  s.w = 2 + k;
  if (setjmp(env) == 0) {
    s.v = 3 + k;
    jump();
  }
  return s.v;
}
/* one member changed, another read: the other keeps its value */
struct AB { int a; int b; };
int t_member_other_kept(int k) {
  struct AB s;
  s.a = 1;
  s.b = 2 + k;
  if (setjmp(env) == 0) {
    s.a = 5;
    jump();
  }
  return s.b;
}
/* UB: the member that was changed, read */
int t_member_changed(int k) {
  struct AB s;
  s.a = 1;
  s.b = 2 + k;
  if (setjmp(env) == 0) {
    s.a = 5;
    jump();
  }
  return s.a;
}
/* a volatile array: its elements keep the values they were changed to */
int t_volatile_array(int k) {
  volatile int a[2];
  a[0] = 1;
  a[1] = 2;
  if (setjmp(env) == 0) {
    a[1] = 7 + k;
    jump();
  }
  return a[0] * 10 + a[1];
}
/* UB: changed in a loop after the setjmp, then the longjmp */
int t_changed_in_loop(int k) {
  int x = 0;
  if (setjmp(env) == 0) {
    for (int i = 0; i < 3; ++i) x = x + i;
    jump();
  }
  return x + k;
}
/* a change that a branch not taken would make: unchanged */
int t_change_not_taken(int k) {
  int x = 4 + k;
  if (setjmp(env) == 0) {
    if (k > 100) x = 0;
    jump();
  }
  return x;
}
/* UB: two setjmps on two buffers, the object changed after the inner one, the longjmp to the outer */
static jmp_buf env2;
int t_nested_setjmp(int k) {
  int x = 1;
  if (setjmp(env) == 0) {
    if (setjmp(env2) == 0) {
      x = 2 + k;
      longjmp(env, 1);
    }
  }
  return x;
}
/* changed again after the first longjmp, read after the second */
int t_changed_after_first_longjmp(int k) {
  volatile int n = 0;
  int x = 1;
  if (setjmp(env) < 2) {
    n = n + 1;
    if (n == 1) longjmp(env, 1);
    x = 3 + k;
    longjmp(env, 2);
  }
  return x;
}
/* rog's audit of auditfix3 (AF1): an object that a callee only reads between the setjmp and the
   longjmp is not changed (7.13.2.1p3), through an int *, a const int * and a member's address;
   the callee's result is not kept, as a variable assigned after the setjmp would be indeterminate */
static int reader(int *p) { return *p + 1; }
static int creader(const int *p) { return *p + 2; }
int t_callee_reads(int k) {
  int x = 5 + k;
  if (setjmp(env) == 0) {
    (void)reader(&x);
    deep(1);
  }
  return x;
}
int t_callee_reads_const(int k) {
  int x = 5 + k;
  if (setjmp(env) == 0) {
    (void)creader(&x);
    deep(1);
  }
  return x;
}
int t_callee_reads_member(int k) {
  struct AB s = {1, 2 + k};
  if (setjmp(env) == 0) {
    (void)reader(&s.b);
    deep(1);
  }
  return s.b;
}
/* a callee's store, the same value included, is a change; a structure's other member is kept */
static void same(int *p) { *p = *p; }
int t_callee_stores_same(int k) {
  int x = 5 + k;
  if (setjmp(env) == 0) {
    same(&x);
    deep(1);
  }
  return x;
}
int t_callee_stores_member(int k) {
  struct AB s = {1, 2 + k};
  if (setjmp(env) == 0) {
    same(&s.a);
    deep(1);
  }
  return s.b;
}
/* a callee's store of the same value through a pointer it got otherwise (a global) */
static int *gpx;
static void same_via_global(void) { *gpx = *gpx; }
int t_callee_global_ptr_same(int k) {
  int x = 5 + k;
  gpx = &x;
  if (setjmp(env) == 0) {
    same_via_global();
    deep(1);
  }
  return x;
}
/* AF2: library models' stores: sscanf's (x set to 2, then back), strtol's end pointer */
int t_sscanf_restore(int k) {
  int x = 1 + k;
  if (setjmp(env) == 0) {
    sscanf("2", "%d", &x);
    sscanf(k ? "2" : "1", "%d", &x);
    deep(1);
  }
  return x;
}
long strtol(const char *, char **, int);
int t_strtol_end(int k) {
  char buf[4] = "12";
  char *e = buf;
  if (setjmp(env) == 0) {
    (void)strtol(buf + k, &e, 10);
    deep(1);
  }
  return e == buf + 2;
}
