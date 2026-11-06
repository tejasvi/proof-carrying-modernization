/* x86 SIMD intrinsics (PACKSSDW, PSLLW / PSRLW by an immediate count, MAXPS, MOVMSKPS) and GCC's
   __builtin_setjmp / __builtin_longjmp (run with CASES=gaps2_cases.txt; a C source). Expected result
   (labelled per case in the cases file): MATCH, or UB from cirrun on the u_ cases (a __builtin_longjmp
   in the function that calls __builtin_setjmp, which GCC rules out; a buffer that holds no
   __builtin_setjmp) and on the g_ gaps (the sign of a NaN; __builtin_frame_address). */
#include <emmintrin.h>
#include <stdint.h>
#include <string.h>

typedef short v8hi __attribute__((vector_size(16)));
typedef int v4si __attribute__((vector_size(16)));

static int sum8(v8hi r) {
  int s = 0;
  for (int i = 0; i < 8; ++i)
    s = s * 3 + r[i];
  return s;
}

int s_packssdw(int k) {
  v4si a = {1, -1, 40000 + k, -40000};
  v4si b = {32767 + k, -32768 - k, 0, 100000};
  return sum8(__builtin_ia32_packssdw128(a, b));
}
int s_pslli(int k) {
  v8hi a = {1, -1, 0x4000, 0x7fff, -32768, 3, 5, 0x1234};
  return sum8(__builtin_ia32_psllwi128(a, 1 + k));
}
int s_psrli(int k) {
  v8hi a = {1, -1, 0x4000, 0x7fff, -32768, 3, 5, 0x1234};
  return sum8(__builtin_ia32_psrlwi128(a, 3 + k));
}
/* through <emmintrin.h>, on __m128i, as UnitTests/Vector/SSE/sse.shift does */
int s_shift_m128i(int k) {
  __m128i ones = _mm_set1_epi32(0);
  ones = _mm_cmpeq_epi32(ones, ones);
  __m128i lo = _mm_srli_epi16(ones, 8 + k);
  __m128i hi = _mm_slli_epi16(ones, 8 + k);
  return _mm_extract_epi16(lo, 1) * 100000 + _mm_extract_epi16(hi, 6);
}
int s_maxps(int k) {
  __m128 a = _mm_setr_ps(1.0f + k, -0.0f, __builtin_nanf(""), 2.0f);
  __m128 b = _mm_setr_ps(0.5f, 0.0f, 1.0f, __builtin_nanf(""));
  __m128 r = _mm_max_ps(a, b);
  float r1 = r[1], r3 = r[3];
  return (int) r[0] * 1000 + (int) __builtin_copysignf(1.0f, r1) * 100 + (int) r[2] * 10 + (r3 != r3);
}
int s_movmskps(int k) {
  return _mm_movemask_ps(_mm_setr_ps(3.0f + k, -0.0f, 2.0f, -1.0f)) * 10 +
         _mm_movemask_ps(_mm_setr_ps(-1.0f, -2.0f, -3.0f, -4.0f - k));
}
/* gap: the sign of a NaN element is not modelled (Float has one NaN) */
int g_movmsk_nan(int k) {
  return _mm_movemask_ps(_mm_setr_ps(__builtin_nanf(""), 1.0f, 2.0f, 3.0f + k));
}

static void *bufA[5];
static void jump_a(void) { __builtin_longjmp(bufA, 1); }

int s_bsj_callee(int k) {
  volatile int n = k;
  if (__builtin_setjmp(bufA) == 0) {
    n += 5;
    jump_a();
    return -1;
  }
  return n + 100;
}

static intptr_t bufB[5];
static void jump_b(int depth) {
  if (depth > 0)
    jump_b(depth - 1);
  __builtin_longjmp((void **) bufB, 1);
}

int s_bsj_intptr(int k) {
  if (!__builtin_setjmp((void **) bufB)) {
    jump_b(3);
    return -1;
  }
  return 20 + k;
}

/* the buffer copied, then the original cleared (gcc-c-torture pr64242) */
static void jump_copy(void *p) {
  void *buf[8];
  memcpy(buf, p, 5 * sizeof(void *));
  memset(p, 0, 5 * sizeof(void *));
  __builtin_longjmp(buf, 1);
}

int s_bsj_copy(int k) {
  void *buf[5];
  if (!__builtin_setjmp(buf))
    jump_copy(buf);
  return 30 + k;
}

/* back to a __builtin_setjmp whose statement has ended (gcc-c-torture built-in-setjmp) */
static void *bufC[20];
static void jump_c(void) { __builtin_longjmp(bufC, 1); }

int s_bsj_after(int k) {
  char s[8] = "test";
  if (__builtin_setjmp(bufC))
    return (int) strlen(s) + 40 + k;
  for (int i = 0; i < 3; ++i)
    jump_c();
  return -1;
}

/* gap: __builtin_frame_address outside __builtin_setjmp is not modelled */
int g_frame_address(int k) {
  void *buf[5];
  buf[0] = __builtin_frame_address(0);
  return (buf[0] != 0) + k;
}

/* undefined: GCC's __builtin_longjmp may only be called from a function that the function calling
   __builtin_setjmp calls */
static void *bufD[5];
int u_bsj_same_fn(int k) {
  if (__builtin_setjmp(bufD) == 0)
    __builtin_longjmp(bufD, 1);
  return k;
}
/* undefined: the buffer holds no __builtin_setjmp */
static void *bufE[5];
static void jump_e(void) { __builtin_longjmp(bufE, 1); }
int u_bsj_unset(int k) {
  jump_e();
  return k;
}
