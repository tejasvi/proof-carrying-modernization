// rog's audit items in C++ (run with CASES=audit2x_cases.txt): F11, a compare-exchange whose failure
// order is stronger than its success order, allowed since C++17 ([atomics.types.operations],
// P0418R2); F13, the pointer conversions of catching by pointer ([except.handle]p3): qualification,
// void *, function pointer conversions and std::nullptr_t, with a derived-to-base conversion, a
// multi-level qualification conversion and a pointer to member catching std::nullptr_t left
// unmodelled. Expected result, labelled per case in the cases file: MATCH, or UB from cirrun.
#include <atomic>
#include <cstddef>

int x_cmpxchg_failure_stronger(int k) {
  std::atomic<int> a{1};
  int e = 1;
  bool ok = a.compare_exchange_strong(e, 2 + k, std::memory_order_relaxed, std::memory_order_seq_cst);
  return ok * 10 + a.load();
}
int x_cmpxchg_weak_failure_acquire(int k) {
  std::atomic<int> a{1};
  int e = 1;
  bool ok = a.compare_exchange_weak(e, 2 + k, std::memory_order_relaxed, std::memory_order_acquire);
  return ok * 10 + a.load();
}
int x_cmpxchg_failure_stronger_fails(int k) {
  std::atomic<int> a{1};
  int e = 5;
  bool ok = a.compare_exchange_strong(e, 2 + k, std::memory_order_release, std::memory_order_seq_cst);
  return ok * 100 + e * 10 + a.load();
}

static int x = 5;
static const int cx = 7;
static void fn() {}
static void fnx() noexcept {}
struct B { int b = 1; };
struct D : B { int d = 2; };
struct S { int m; };
static D dobj;

int h_const_ptr(int k) {
  try { throw &x; } catch (const int *p) { return *p + k; } catch (...) { return -1; }
}
int h_volatile_const_ptr(int k) {
  try { throw &x; } catch (const volatile int *p) { return *p + k; } catch (...) { return -1; }
}
int h_void_ptr(int k) {
  try { throw &x; } catch (void *p) { return (p == &x) + k; } catch (...) { return -1; }
}
int h_const_void_of_const(int k) {
  try { throw &cx; } catch (const void *p) { return (p == &cx) + k; } catch (...) { return -1; }
}
// no match: the qualification would be dropped; the next handler
int h_drop_const(int k) {
  try { throw &cx; } catch (int *) { return 1; } catch (const int *p) { return *p + k; }
}
// no match: void * does not catch a function pointer
int h_void_of_fnptr(int k) {
  try { throw &fn; } catch (void *) { return 1; } catch (...) { return 2 + k; }
}
// no match between unrelated pointer types (double * does not catch int *)
int h_other_pointee(int k) {
  try { throw &x; } catch (double *) { return 1; } catch (int *p) { return *p + k; }
}
int h_nullptr_as_ptr(int k) {
  try { throw nullptr; } catch (int *p) { return (p == nullptr) + k; } catch (...) { return -1; }
}
int h_nullptr_as_const_char_ptr(int k) {
  try { throw nullptr; } catch (const char *p) { return (p == nullptr) + k; } catch (...) { return -1; }
}
int h_nullptr_as_member_ptr(int k) {
  try { throw nullptr; } catch (int S::*p) { return (p == nullptr) + k; } catch (...) { return -1; }
}
int h_noexcept_fnptr(int k) {
  try { throw &fnx; } catch (void (*p)()) { p(); return 3 + k; } catch (...) { return -1; }
}
int h_exact_ptr(int k) {
  try { throw &x; } catch (int *p) { return *p + k; } catch (...) { return -1; }
}
// a pointer to a derived class caught as a pointer to its base: not modelled
int h_derived_as_base(int k) {
  try { throw &dobj; } catch (B *p) { return p->b + k; } catch (...) { return -1; }
}
// a multi-level qualification conversion: not modelled
int h_multilevel(int k) {
  static int *px = &x;
  try { throw &px; } catch (const int *const *p) { return **p + k; } catch (...) { return -1; }
}
