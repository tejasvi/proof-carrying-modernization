// Builtins and math functions that ClangIR keeps as operations:
// cir.clz / cir.ctz, cir.is_constant, cir.ceil / cir.round / cir.fabs /
// cir.floor / cir.sqrt, cir.is_fp_class, and bit-fields.
#include <cmath>

int t_clz(int x) { return __builtin_clz((unsigned)x); }
int t_ctz(int x) { return __builtin_ctz((unsigned)x); }
int t_clzll(int x) { return __builtin_clzll((unsigned long long)x); }
int t_isconst(int x) { return __builtin_constant_p(x) ? 1 : 2; }
int t_ceil(int a, int b) { return (int)std::ceil((double)a / b); }
int t_floor(int a, int b) { return (int)std::floor((double)a / b); }
int t_round(int a, int b) { return (int)std::round((double)a / b); }
int t_fabs(int a) { return (int)std::fabs((double)a * 1.5); }
int t_sqrt(int a) { return (int)std::sqrt((double)a); }
int t_isnan(int a, int b) {
  double x = (double)a / b;
  return (std::isnan(x) ? 1 : 0) + (std::isinf(x) ? 10 : 0) + (std::isfinite(x) ? 100 : 0);
}

struct Flags { unsigned a : 3; int b : 5; unsigned c : 8; };
int t_bitfield(int n) {
  Flags f;
  f.a = n;
  f.b = n - 20;
  f.c = n * 3;
  return f.a * 10000 + f.b * 100 + f.c;
}
int t_bitfield_set(int n) {
  Flags f;
  f.c = 7;
  int r = (f.a = n);
  return r * 1000 + f.c;
}

#include <atomic>
#include <cstdlib>
#include <stdexcept>
int t_mulov(int a, int b) {
  int r;
  bool o = __builtin_mul_overflow(a, b, &r);
  return o ? -1 : r;
}
int t_addov(int a, int b) {
  unsigned r;
  bool o = __builtin_add_overflow((unsigned)a, (unsigned)b, &r);
  return o ? -1 : (int)(r % 1000);
}
int t_abs(int a) { return std::abs(a); }
int t_atomic(int n) {
  std::atomic<int> c{n};
  c.fetch_add(5);
  return c.fetch_sub(1);
}
int t_except(int n) {
  try {
    if (n > 3) throw std::length_error("too big");
    return n;
  } catch (const std::length_error &) {
    return -1;
  }
}

#include <cctype>
int t_ctype(int c) {
  return (isdigit(c) ? 1 : 0) + (isalpha(c) ? 2 : 0) + (isalnum(c) ? 4 : 0) + (isspace(c) ? 8 : 0) +
         (isupper(c) ? 16 : 0) + (islower(c) ? 32 : 0) + (isxdigit(c) ? 64 : 0) +
         (ispunct(c) ? 128 : 0) + (isprint(c) ? 256 : 0);
}
int t_case(int c) { return toupper(c) * 1000 + tolower(c); }
