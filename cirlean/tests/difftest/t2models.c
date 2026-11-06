// Tier 2 of the external models (CASES=t2models_cases.txt): sched_get_priority_max/min,
// pthread_setschedparam, errno (__errno_location), GNU strerror_r, time and ctime_r; and errno after
// the C library models whose glibc versions set it (strtod, strtol, <math.h>, sscanf, the printf
// family's encoding errors, perror). The cases
// labelled "environment" depend on the machine: a real-time policy needs a privilege that the model
// assumes, time() reads the clock, and ctime_r the time zone (the model's is UTC, as this machine's).
#define _GNU_SOURCE
#include <errno.h>
#include <math.h>
#include <pthread.h>
#include <sched.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <wchar.h>

// a short digest of a C string (its characters, in order)
static unsigned digest(const char *s) {
  unsigned h = 7;
  for (; *s; ++s) h = h * 31u + (unsigned char)*s;
  return h % 100000u;
}

// --- sched_get_priority_max/min: Linux's values; -1 and errno EINVAL for a policy that is not one
// (errno is 7 before each call: a success leaves it)
int t_sched_prio(int p) {
  errno = 7;
  int mx = sched_get_priority_max(p);
  int e1 = errno;
  errno = 7;
  int mn = sched_get_priority_min(p);
  int e2 = errno;
  return mx * 10000 + mn * 100 + e1 + e2;
}

// --- pthread_setschedparam on the thread itself: the error number, which glibc also leaves in errno;
// errno unchanged on success (1234 before)
int t_setsched(int pol, int prio) {
  struct sched_param sp;
  sp.sched_priority = prio;
  errno = 1234;
  int r = pthread_setschedparam(pthread_self(), pol, &sp);
  return r * 10000 + errno;
}

// a real-time policy with a priority in range: 0 with the privilege, EPERM without it
int t_setsched_rt(int prio) {
  struct sched_param sp;
  sp.sched_priority = prio;
  int r = pthread_setschedparam(pthread_self(), SCHED_FIFO, &sp);
  return r == 0 || r == EPERM;
}

// UB: an id that is no thread's (glibc reads the thread descriptor at that address)
int ub_setsched_null_thread(int x) {
  struct sched_param sp;
  sp.sched_priority = 0;
  return pthread_setschedparam((pthread_t)0, SCHED_OTHER, &sp) + x;
}

// --- errno: 0 at program start (C11 7.5p3), one object, which __errno_location returns each time
int t_errno(int x) {
  int start = errno;
  errno = x;
  int *p = &errno;
  int *q = &errno;
  return start * 1000 + (p == q) * 100 + *p;
}

// --- strerror_r (GNU): glibc's message for a number it knows, a string of its own (buf unused);
// else "Unknown error N" in buf, and buf
int t_strerror(int e) {
  char buf[64];
  buf[0] = 'Z';
  buf[1] = 0;
  char *r = strerror_r(e, buf, sizeof buf);
  return (int)(digest(r) * 10 + (r == buf) * 2 + (buf[0] == 'Z'));
}

// a buffer of 8: the unknown number's text cut to 7 characters, a known message whole
int t_strerror_small(int e) {
  char buf[8];
  char *r = strerror_r(e, buf, sizeof buf);
  return (int)(digest(r) * 10 + (r == buf) * 2);
}

// a length of 0: nothing written
int t_strerror_zero(int e) {
  char buf[4] = "Z";
  char *r = strerror_r(e, buf, 0);
  return (r == buf) * 10 + (buf[0] == 'Z');
}

// UB: a length larger than the buffer, which the text overflows
int ub_strerror_overflow(int e) {
  char buf[4];
  char *r = strerror_r(e, buf, 64);
  return (int)digest(r);
}

// glibc's message is a string of its own, which outlives the block of the call
int t_strerror_outlives(int e) {
  char *r;
  {
    char buf[64];
    r = strerror_r(e, buf, sizeof buf);
  }
  return (int)digest(r);
}

// --- time reads the clock (environment): relations only; the result and the value stored agree, and
// a second reading is not earlier
int t_time_store(int x) {
  time_t t = -1;
  time_t r = time(&t);
  return (r == t) * 10 + x;
}
int t_time_null(int x) {
  time_t a = time(NULL);
  time_t b = time(NULL);
  return (b >= a) * 10 + x;
}

// environment: the model's clock reads the Epoch (World.now = 0)
int t_time_epoch(int x) { return (time(NULL) == 0) * 10 + x; }

// --- ctime_r: asctime's text of the local time (UTC here and in the model), 01:02:03 on the day
// `days` after 1970-01-01
int t_ctime(int days) {
  time_t t = (time_t)days * 86400 + 3723;
  char buf[26];
  char *r = ctime_r(&t, buf);
  if (r != buf) return -1;
  return (int)(digest(buf) * 100 + strlen(buf));
}

// a year of 5 or more characters: the text needs more than 26 bytes, so null with errno EOVERFLOW,
// and buf holds its first 25 characters
int t_ctime_overflow(int days) {
  time_t t = (time_t)days * 86400 + 3723;
  char buf[26];
  errno = 0;
  char *r = ctime_r(&t, buf);
  return (r == NULL) * 1000000 + (errno == EOVERFLOW) * 100000 + (int)(digest(buf) % 1000) * 100 +
         (int)strlen(buf);
}

// a year beyond struct tm's int: null with errno EINVAL (localtime_r fails, asctime_r of null)
int t_ctime_huge(int x) {
  time_t t = (time_t)1 << 62;
  char buf[26];
  errno = 0;
  char *r = ctime_r(&t, buf);
  return (r == NULL) * 100 + errno + x;
}

// ctime_r of time()'s value, as Thrift's errorTimeWrapper uses it: a 4-digit year, '\n' at index 24
int t_ctime_now(int x) {
  time_t t;
  time(&t);
  char buf[26];
  char *r = ctime_r(&t, buf);
  return (r == buf) * 100 + (buf[24] == '\n') * 10 + (strlen(buf) == 25) + x;
}

// UB: a buffer of 10 bytes for the 26 of the text
int ub_ctime_small(int days) {
  time_t t = (time_t)days * 86400;
  char buf[10];
  char *r = ctime_r(&t, buf);
  return r == buf;
}

// --- errno of the C library models whose glibc versions set it, now that the program can read it
// strtod, strtof: ERANGE for an overflow, and for an underflow (tiny after rounding and inexact)
static const char *const fp_inputs[] = {
  "1e309", "1.7976931348623157e308", "1.7976931348623159e308", "1e-400", "-1e-400", "1e-310",
  "0x1p-1074", "0x1.8p-1074", "2.2250738585072011e-308", "2.2250738585072013e-308", "inf", "nan",
  "0e-999", "1.5"};
int t_strtod_erange(int k) {
  char *end;
  errno = 0;
  strtod(fp_inputs[k], &end);
  return errno == ERANGE;
}
static const char *const fp_inputs_f[] = {"1e-40", "1e-50", "3.4e38", "3.5e38", "0x1p-149", "1e-38"};
int t_strtof_erange(int k) {
  char *end;
  errno = 0;
  strtof(fp_inputs_f[k], &end);
  return errno == ERANGE;
}
// atof: an underflow is a result, 0 here, and glibc's strtod stores ERANGE
int t_atof_underflow(int k) {
  errno = 0;
  volatile double r = atof(k ? "-1e-400" : "1e-400");
  return errno * 10 + (r == 0);
}
// UB: atof of a value that cannot be represented, an overflow (C11 7.22.1p1; glibc: HUGE_VAL, ERANGE)
int ub_atof_overflow(int k) {
  errno = 0;
  volatile double r = atof(k ? "-1e999" : "1e999");
  return errno * 10 + (r > 1 || r < -1);
}
// strtol, strtoul: ERANGE out of range
static const char *const int_inputs[] = {"9223372036854775807", "9223372036854775808",
  "-9223372036854775808", "-9223372036854775809", "18446744073709551615", "18446744073709551616",
  "-18446744073709551615", "-18446744073709551616"};
int t_strtol_erange(int k) {
  char *end;
  errno = 0;
  if (k < 4) strtol(int_inputs[k], &end, 10);
  else strtoul(int_inputs[k], &end, 10);
  return errno == ERANGE;
}

// <math.h>: EDOM for a domain error, ERANGE for a pole or an overflow, errno left otherwise
static volatile double a1[] = {-1.0, 0.0, 1000.0, 2.0, 0.5, 1.0, 4.0, 10.0, -1000.0, 2000.0};
int t_libm_errno(int k) {
  errno = 7;
  volatile double r = 0;
  switch (k) {
  case 0: r = sqrt(a1[0]); break;        // EDOM
  case 1: r = log(a1[1]); break;         // pole: ERANGE
  case 2: r = log(a1[0]); break;         // EDOM
  case 3: r = exp(a1[2]); break;         // overflow: ERANGE
  case 4: r = pow(a1[7], 400 * a1[5]); break;  // overflow: ERANGE
  case 5: r = pow(a1[1], a1[0]); break;  // pole: ERANGE
  case 6: r = pow(a1[0], a1[4]); break;  // EDOM
  case 7: r = fmod(a1[5], a1[1]); break; // EDOM
  case 8: r = asin(a1[3]); break;        // EDOM
  case 9: r = acos(-a1[3]); break;       // EDOM
  case 10: r = atanh(a1[5]); break;      // pole: ERANGE
  case 11: r = atanh(a1[3]); break;      // EDOM
  case 12: r = acosh(a1[4]); break;      // EDOM
  case 13: r = cosh(a1[2]); break;       // overflow: ERANGE
  case 14: r = sinh(a1[8]); break;       // overflow: ERANGE
  case 15: r = exp2(a1[9]); break;       // overflow: ERANGE
  case 16: r = sin(a1[2] / a1[1]); break;  // sin(inf): EDOM
  case 17: r = sqrt(a1[6]); break;       // none
  case 18: r = log(a1[5]); break;        // none (0 exactly)
  case 19: r = floor(-a1[4]); break;     // none
  case 20: r = expf((float)(a1[2] / 10)); break;  // float overflow: ERANGE
  case 21: r = sqrtf((float)a1[0]); break;        // EDOM
  case 22: r = logf((float)a1[1]); break;         // ERANGE
  }
  (void)r;
  return errno;
}

// UB: errno after a possible underflow (glibc's rule differs between functions; here exp of -1000
// underflows to 0)
int ub_libm_errno_underflow(int x) {
  errno = 7;
  volatile double r = exp(a1[8]);
  (void)r;
  return errno + x;
}

// the functions Lean's Float lacks (hypot, hypotf, expm1, log1p, erf, erfc, tgamma, lgamma): errno as
// after the others
static volatile double a2[] = {1.5e308, -1.0, -2.0, 1000.0, 0.0, 30.0, 1.0, 0.5, 3.0e38, 250.0, 1e308};
int t_libm1_errno(int k) {
  errno = 7;
  volatile double r = 0;
  switch (k) {
  case 0: r = hypot(a2[0], a2[0]); break;                  // overflow: ERANGE
  case 1: r = hypotf((float)a2[8], (float)a2[8]); break;   // float overflow: ERANGE
  case 2: r = expm1(a2[3]); break;                         // overflow: ERANGE
  case 3: r = log1p(a2[1]); break;                         // pole: ERANGE
  case 4: r = log1p(a2[2]); break;                         // EDOM
  case 5: r = tgamma(a2[4]); break;                        // pole: ERANGE
  case 6: r = tgamma(a2[1]); break;                        // a negative integer: EDOM
  case 7: r = tgamma(a2[9]); break;                        // overflow: ERANGE
  case 8: r = lgamma(a2[4]); break;                        // pole: ERANGE
  case 9: r = lgamma(a2[2]); break;                        // pole: ERANGE
  case 10: r = erf(a2[7]); break;                          // none
  case 11: r = erfc(a2[6]); break;                         // none
  case 12: r = hypot(a2[6], a2[7]); break;                 // none
  case 13: r = hypot(a2[10], a2[10]); break;               // none: 1.414e308 is finite
  }
  (void)r;
  return errno;
}

// UB: errno after erfc(30), which underflows to 0 (glibc stores ERANGE; the model leaves errno
// indeterminate)
int ub_libm1_errno_underflow(int x) {
  errno = 7;
  volatile double r = erfc(a2[5]);
  (void)r;
  return errno + x;
}

// sscanf: errno left after a floating conversion in range; indeterminate (UB to read) after one that
// may have overflowed or underflowed
int t_sscanf_errno(int x) {
  double d;
  errno = 7;
  int n = sscanf("0.5", "%lf", &d);
  return n * 100 + errno + x;
}
int ub_sscanf_errno_overflow(int x) {
  double d;
  errno = 0;
  int n = sscanf("1e400", "%lf", &d);
  return n * 100 + errno + x;
}

// printf-family encoding errors (%lc of a wide character the C locale does not have): the result is
// negative and errno EILSEQ (wcrtomb, C11 7.29.6.3.3p4); sprintf writes the text before the error
int t_lc_eilseq(int k) {
  char b[8] = "zzzzzzz";
  wint_t c = 0xE9;
  errno = 0;
  int r = k == 0 ? sprintf(b, "%lc", c)
        : k == 1 ? snprintf(b, sizeof b, "%lc", c)
        : k == 2 ? snprintf(b, 0, "%lc", c)
        : k == 3 ? fprintf(stderr, "%lc", c)
        : sprintf(b, "ab%lc", c);
  return errno * 100 + (r < 0) * 10 + (strcmp(b, "ab") == 0);
}

// UB: errno after perror, which C11 7.5p3 lets set it to any nonzero value (glibc leaves EINVAL when
// stderr is not open for reading, as under the test runner, else 5)
int ub_perror_errno(int k) {
  errno = 5;
  perror(k ? "t2models" : 0);
  return errno;
}
