/* __builtin_setjmp's buffer and __builtin_longjmp's limits (run with CASES=gaps6_cases.txt; a C
   source). Expected result (labelled per case in the cases file): MATCH, or UB from cirrun on the u_
   cases (a buffer shorter than GCC's five words, which CIR's code for the builtin writes past) and on
   the gap g_bsj_reraise (a __builtin_longjmp to a buffer a caller set, from a function that calls
   __builtin_setjmp too: GCC allows it, it is not modelled). */
#include <stdint.h>

static intptr_t buf5[5];
static void jump5(void) { __builtin_longjmp((void **) buf5, 1); }

int t_bsj_five(int k) {
  if (__builtin_setjmp((void **) buf5) == 0) {
    jump5();
    return -1;
  }
  return 60 + k;
}

/* undefined: two words, where CIR's code for __builtin_setjmp stores words 0 and 2 */
static intptr_t buf2[2];
static void jump2(void) { __builtin_longjmp((void **) buf2, 1); }
int u_bsj_short(int k) {
  if (__builtin_setjmp((void **) buf2) == 0) {
    jump2();
    return -1;
  }
  return 70 + k;
}

/* gap: a handler that re-raises to its caller's buffer */
static void *outer[5];
static void *inner[5];
static void thrower(void) { __builtin_longjmp(inner, 1); }
static void reraiser(void) {
  if (__builtin_setjmp(inner) == 0)
    thrower();
  else
    __builtin_longjmp(outer, 1);
}
int g_bsj_reraise(int k) {
  if (__builtin_setjmp(outer) == 0) {
    reraiser();
    return -1;
  }
  return 50 + k;
}
