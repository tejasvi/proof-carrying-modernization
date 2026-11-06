/* Null pointer arithmetic in C (run with CASES=contb_cases.txt): undefined, unlike C++
   (contb.cpp's n_ cases). C11 6.5.6p8 and p9 ask for pointers into an array object, which a null
   pointer is not. Expected result: UB from cirrun (native runs print the GCC result). */
#include <stddef.h>

/* the difference of two null pointers (C11 6.5.6p9) */
int nc_null_diff(int k) {
  int *p = NULL, *q = NULL;
  return (int)(p - q) + k;
}
/* a null pointer plus 0 (C11 6.5.6p8) */
int nc_null_plus_zero(int k) {
  int *p = NULL;
  int *r = p + k;
  return r == NULL;
}
