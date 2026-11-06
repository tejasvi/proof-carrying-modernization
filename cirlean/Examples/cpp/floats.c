/* Floating point in tests: conversions to integers (with cJSON's saturation),
   floor/ceil, rounding to float, cJSON's print_number dance (%1.15g, read
   back with %lg, else %1.17g) and other printf conversions; all checked by
   the kernel (Examples/Floats.lean). */
#include <stdio.h>
#include <math.h>
#include <limits.h>
static int to_int(double number) {
  if (number >= INT_MAX) return INT_MAX;
  else if (number <= (double)INT_MIN) return INT_MIN;
  return (int)number;
}
int t_conv(void) {
  double d = 12345.678;
  float f = (float)d;
  return to_int(d) + to_int(floor(-2.5)) + to_int(ceil(2.1)) + to_int((double)f * 10.0);
}
int t_print(void) {
  char buf[26];
  double test = 0.0;
  double d = 0.1;
  int n = sprintf(buf, "%1.15g", d);
  if (sscanf(buf, "%lg", &test) != 1 || test != d) n = sprintf(buf, "%1.17g", d);
  return n * 100 + buf[0] + buf[2];
}
int t_print2(void) {
  char buf[64];
  return sprintf(buf, "%d|%5.2f|%e", 42, 3.14159, 1e-10);
}
