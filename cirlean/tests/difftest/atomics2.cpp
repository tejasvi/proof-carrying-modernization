// Atomic exchange and compare-exchange (run with CASES=atomics2_cases.txt):
// __atomic_exchange_n / __atomic_compare_exchange_n lower to cir.atomic.xchg /
// cir.atomic.cmpxchg. Their sequential meaning, exact with one thread: xchg
// stores the new value and returns the old one; cmpxchg stores the desired
// value if the object holds the expected one (true), else writes the object's
// value back to *expected (false); weak and strong are the same. Expected
// result (labelled per case in the cases file): MATCH on the a_* cases, UB from
// cirrun on the u_* controls (a punned access to a struct member, an
// indeterminate object); native runs print the GCC result.

struct Cnt { int use; int weak; };

// int exchange: the old value, and the new one stored
int a_xchg_int(int a, int b) {
  int x = a;
  int old = __atomic_exchange_n(&x, b, __ATOMIC_ACQ_REL);
  return old * 1000 + x;
}

// long exchange
int a_xchg_long(int a, int b) {
  long x = (long)a << 33;
  long old = __atomic_exchange_n(&x, (long)b, __ATOMIC_SEQ_CST);
  return (int)((old >> 33) * 1000 + x);
}

// pointer exchange
int a_xchg_ptr(int a, int b) {
  int u = a, v = b;
  int *p = &u;
  int *old = __atomic_exchange_n(&p, &v, __ATOMIC_ACQ_REL);
  return *old * 1000 + *p;
}

// int compare-exchange: c != 0 expects the object's value (success, the
// desired value stored), c == 0 expects another (failure, expected gets the
// object's value)
int a_cas_int(int a, int b, int c) {
  int x = a, e = c ? a : a + 1;
  bool ok = __atomic_compare_exchange_n(&x, &e, b, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
  return ok * 1000000 + x * 1000 + e;
}

// long compare-exchange, both outcomes
int a_cas_long(int a, int b, int c) {
  long x = (long)a << 32;
  long e = c ? x : x + 1;
  bool ok = __atomic_compare_exchange_n(&x, &e, (long)b, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
  return ok * 1000000 + (int)(x % 997) * 1000 + (int)(e % 991);
}

// pointer compare-exchange, both outcomes (the expected pointer is the object's
// or another object's)
int a_cas_ptr(int a, int b, int c) {
  int u = a, v = b, w = 0;
  int *p = &u;
  int *e = c ? &u : &w;
  bool ok = __atomic_compare_exchange_n(&p, &e, &v, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
  return ok * 1000 + *p * 10 + *e;
}

// the weak form in a loop, as libstdc++'s weak_ptr::lock increments a use count
// unless it is zero (_M_add_ref_lock_nothrow)
int a_weak_loop(int a) {
  int count = a;
  int cur = __atomic_load_n(&count, __ATOMIC_RELAXED);
  int tries = 0;
  do {
    if (cur == 0) return -1;
    tries++;
  } while (!__atomic_compare_exchange_n(&count, &cur, cur + 1, true, __ATOMIC_ACQ_REL, __ATOMIC_RELAXED));
  return count * 10 + tries;
}

// exchange and compare-exchange on struct members of their own type
int a_member_ops(int a, int b) {
  Cnt c = {a, b};
  int old = __atomic_exchange_n(&c.use, a + b, __ATOMIC_ACQ_REL);
  int e = b;
  bool ok = __atomic_compare_exchange_n(&c.weak, &e, 3, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
  return old * 10000 + ok * 1000 + c.use * 10 + c.weak;
}

// control: a long long exchange over two int members (a punned access)
int u_xchg_punned(int a, int b) {
  Cnt c = {a, b};
  long long old = __atomic_exchange_n((long long *)&c.use, 0LL, __ATOMIC_ACQ_REL);
  return (int)(old % 1000003);
}

// control: a long long compare-exchange over two int members (a punned access)
int u_cas_punned(int a, int b) {
  Cnt c = {a, b};
  long long e = ((long long)b << 32) | (unsigned)a;
  bool ok = __atomic_compare_exchange_n((long long *)&c.use, &e, 0LL, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
  return ok * 1000 + c.use + c.weak;
}

// control: an exchange on an indeterminate object (never written)
int u_xchg_indeterminate(int b) {
  int x;
  int old = __atomic_exchange_n(&x, b, __ATOMIC_ACQ_REL);
  return old == 12345 ? 1 : x;
}
