// Builtins on integers and floats: GCC's (cir.popcount, cir.parity, cir.ffs, cir.clrsb,
// cir.byte_swap, cir.copysign, fmax / fmin as cir.fmaxnum / cir.fminnum, cir.prefetch), Clang's
// rotations and bit reversal (cir.rotate, cir.bitreverse), clz / ctz of 0 behind a fallback
// (std::countl_zero); variable-length arrays (an alloca with a size, between cir.stacksave and
// cir.stackrestore); va_copy (cir.va_copy); the C library's strdup and getchar (standard input
// at its end).
#include <bit>
#include <cmath>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>

int t_popcount(int x) { return __builtin_popcount((unsigned)x); }
int t_popcountll(int x, int y) {
  return __builtin_popcountll(((unsigned long long)(unsigned)x << 32) | (unsigned)y);
}
int t_popcount16(int x) { return __builtin_popcountg((unsigned short)x); }
int t_parity(int x) { return __builtin_parity((unsigned)x) + 10 * __builtin_parityll((long long)x * x); }
int t_ffs(int x) { return __builtin_ffs(x) + 100 * __builtin_ffsll((long long)x * 2147483648LL); }
int t_clrsb(int x) { return __builtin_clrsb(x) + 100 * __builtin_clrsbll((long long)x * 65536); }
int t_bswap(int x) {
  unsigned short h = __builtin_bswap16((unsigned short)x);
  unsigned w = __builtin_bswap32((unsigned)x);
  unsigned long long d = __builtin_bswap64((unsigned long long)(unsigned)x);
  return (int)(h ^ (w >> 16) ^ (unsigned)(d >> 40));
}
int t_bswap_signed(int x) { return (int)__builtin_bswap32((unsigned)x) + (short)__builtin_bswap16((unsigned short)x); }

int t_copysign(int a, int b) {
  double r = copysign((double)a, (double)b);
  float rf = copysignf((float)a / 2, (float)b);
  return (int)r * 100 + (int)(rf * 2);
}
int t_copysign_zero(int b) {
  double z = copysign(0.0, (double)b);
  double n = copysign(-0.0, (double)b);
  return std::signbit(z) * 10 + std::signbit(n) + (z == 0.0) * 100;
}
int t_copysign_nan(int b) {
  // NaN signs are not modelled (`Float` has a single NaN): only the class is compared
  double x = copysign(NAN, (double)b);
  return std::isnan(x) * 10 + (int)copysign((double)b, 1.0);
}

int t_vla_loop(int n) {
  int s = 0;
  for (int i = 1; i <= n; ++i) {
    int a[i];
    for (int j = 0; j < i; ++j) a[j] = j + i;
    s += a[i - 1] + (int)(sizeof(a) / sizeof(a[0]));
  }
  return s;
}
int t_vla_2d(int n, int m) {
  int a[n][m];
  for (int i = 0; i < n; ++i)
    for (int j = 0; j < m; ++j) a[i][j] = i * 10 + j;
  int s = 0;
  for (int i = 0; i < n && i < m; ++i) s += a[i][i];
  return s * 100 + a[n - 1][m - 1];
}
int t_vla_break(int n) {
  int s = 0;
  for (int i = 1;; ++i) {
    int a[i];
    a[0] = i * 100;
    a[i - 1] = i;
    s += a[i - 1];
    if (s > n) break;
    if (i % 2) continue;
    s += a[0];
  }
  return s;
}
static int vla_sum(int n) {
  long v[n];
  for (int i = 0; i < n; ++i) v[i] = i * i;
  long s = 0;
  for (int i = 0; i < n; ++i) s += v[i];
  return (int)s;
}
int t_vla_calls(int n) {
  int s = 0;
  for (int i = 1; i <= n; ++i) s += vla_sum(i);
  return s;
}

static int sum_twice(int n, ...) {
  va_list ap, aq;
  va_start(ap, n);
  va_copy(aq, ap);
  int s = 0;
  for (int i = 0; i < n; ++i) s += va_arg(ap, int);
  int t = 0;
  for (int i = 0; i < n; ++i) t += va_arg(aq, int) * 10;
  va_end(aq);
  va_end(ap);
  return s + t;
}
static int copy_midway(int n, ...) {
  va_list ap, aq;
  va_start(ap, n);
  int first = va_arg(ap, int);
  va_copy(aq, ap);
  int x = va_arg(ap, int);
  int y = va_arg(aq, int);
  int z = va_arg(aq, int);
  va_end(aq);
  va_end(ap);
  return first * 1000 + x * 100 + y * 10 + z;
}
int t_va_copy(int a, int b) { return sum_twice(3, a, b, 7); }
int t_va_copy_midway(int a, int b) { return copy_midway(4, a, b, a + b, 9); }

int t_strdup(int k) {
  const char *s = "hello";
  char *d = strdup(s);
  d[0] = 'j';
  int r = (int)strlen(d) * 1000 + d[k] + (s[0] == 'h') * 100000;
  free(d);
  return r;
}
int t_strdup_empty(int k) {
  char *d = strdup("");
  int r = (int)strlen(d) + d[0] + k;
  free(d);
  return r;
}
int t_getchar(int k) { int c = getchar(); return c + k; }
int t_getchar_eof(int k) { return (getchar() == EOF) * 10 + (getchar() == EOF) + k; }

// Clang's rotate and bit-reverse builtins (cir.rotate, cir.bitreverse); GCC has neither, the
// native side computes them with shifts
#ifdef __clang__
#define ROTL32 __builtin_rotateleft32
#define ROTR64 __builtin_rotateright64
#define ROTL8 __builtin_rotateleft8
#define BITREV32 __builtin_bitreverse32
#define BITREV16 __builtin_bitreverse16
#define BITREV8 __builtin_bitreverse8
#else
static unsigned ROTL32(unsigned x, unsigned n) { n %= 32; return n ? (x << n) | (x >> (32 - n)) : x; }
static unsigned long long ROTR64(unsigned long long x, unsigned long long n) {
  n %= 64;
  return n ? (x >> n) | (x << (64 - n)) : x;
}
static unsigned char ROTL8(unsigned char x, unsigned char n) {
  n %= 8;
  return n ? (unsigned char)((x << n) | (x >> (8 - n))) : x;
}
static unsigned long long bitrev(unsigned long long x, int w) {
  unsigned long long r = 0;
  for (int i = 0; i < w; ++i) { r = (r << 1) | (x & 1); x >>= 1; }
  return r;
}
static unsigned BITREV32(unsigned x) { return (unsigned)bitrev(x, 32); }
static unsigned short BITREV16(unsigned short x) { return (unsigned short)bitrev(x, 16); }
static unsigned char BITREV8(unsigned char x) { return (unsigned char)bitrev(x, 8); }
#endif
int t_rotate(int x, int n) {
  unsigned l = ROTL32((unsigned)x, (unsigned)n);
  unsigned long long r = ROTR64((unsigned long long)(unsigned)x, (unsigned long long)n);
  unsigned char b = ROTL8((unsigned char)x, (unsigned char)n);
  return (int)(l ^ (unsigned)(r >> 32) ^ (unsigned)r ^ b);
}
int t_bitreverse(int x) {
  return (int)(BITREV32((unsigned)x) ^ BITREV16((unsigned short)x) ^ BITREV8((unsigned char)x));
}
int t_fmax(int a, int b) {
  double x = a, y = b;
  float fx = a / 2.0f, fy = b / 2.0f;
  return (int)fmax(x, y) * 100 + (int)fmin(x, y) * 10 + (int)(fmaxf(fx, fy) * 2) - (int)(fminf(fx, fy) * 2);
}
int t_fmax_nan(int a) {
  double x = fmax(NAN, (double)a), y = fmin((double)a, NAN);
  return (int)x * 10 + (int)y + std::isnan(fmax(NAN, NAN)) * 1000;
}
int t_fmax_zero(int a) {
  // zeros of both signs: glibc returns the second operand
  double p = 0.0, n = -0.0;
  return std::signbit(fmax(p, n)) * 1000 + std::signbit(fmax(n, p)) * 100 + std::signbit(fmin(p, n)) * 10 +
         std::signbit(fmin(n, p)) + a * 0;
}
int t_prefetch(int x) {
  int a[4] = {x, 2, 3, 4};
  __builtin_prefetch(&a[1]);
  __builtin_prefetch(&a[2], 1, 0);
  return a[0] + a[1];
}
int t_clz_fallback(int x) {
  // std::countl_zero / countr_zero and __builtin_clzg(x, d): cir.clz / cir.ctz poison_zero,
  // then a select of the fallback for 0
  unsigned u = (unsigned)x;
  int l = std::countl_zero(u), r = std::countr_zero(u), w = (int)std::bit_width(u);
  return ((l * 100 + r) * 100 + w) * 100 + __builtin_clzg((unsigned short)x, -1) + 1;
}
