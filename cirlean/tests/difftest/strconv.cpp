// strtod, strtof, strtold, strtol, strtoul, strtoll, strtoull, atof, atoi,
// atol, atoll against glibc (C11 7.22.1): leading white space (isspace),
// signs, decimal and hexadecimal floating input, inf/infinity/nan/nan(...)
// spellings, bases 0 and 2..36, *endptr (nptr itself when there is no subject
// sequence, else just past it, also on overflow), saturation on overflow,
// negated unsigned values, correct rounding (ties to even, ties decided by
// digits far past the 17th, the subnormal boundary), and ERANGE (errno only in
// t_errno). glibc 2.38+ gives strtol and friends C23's 0b prefix when
// _GNU_SOURCE is defined, as g++ and clang++ do. ub_* cases are undefined
// behaviour, not expected to match. A result is (characters consumed) *
// 10^6 or 10^7 + an exact identity of the value.
#include <cerrno>
#include <cfloat>
#include <climits>
#include <cstdlib>
#include <cstring>

// exact identity of a double: NaN, signed zeros (by 1/d, as IEEE), infinities,
// else sign, binary exponent and 52-bit fraction found by exact scaling; the
// sign of a NaN is checked on its own (t_nansign)
static int fp_id(double d) {
  if (d != d) return 1;
  if (d == 0.0) return 1.0 / d < 0.0 ? 4 : 3;
  if (d > DBL_MAX) return 5;
  if (d < -DBL_MAX) return 6;
  unsigned long long s = d < 0.0;
  if (s) d = -d;
  long long e = 0;
  while (d >= 2.0) {
    d *= 0.5;
    ++e;
  }
  while (d < 1.0) {
    d *= 2.0;
    --e;
  }
  unsigned long long m = (unsigned long long)((d - 1.0) * 4503599627370496.0);
  unsigned long long h = m * 0x9E3779B97F4A7C15ull ^ (unsigned long long)(e + 2000) * 0xC2B2AE3D27D4EB4Full ^ s;
  return (int)((h ^ (h >> 32)) % 999983u) + 10;
}
static int fold(unsigned long long u) { return (int)(u % 9999991ull); }

// 7.22.1.3: hex significands round to nearest even at 53 bits, also into the
// subnormal range and at the overflow threshold; an exponent part needs
// digits ("0x1p" stops before p) and "0x" alone is the subject "0"; infinity
// may stop after "inf"; nan(n-char-sequence) needs alphanumerics or _, else
// only "nan" is the subject ("-nan": its sign in t_nansign); decimal ties
// and near-ties at 2^53, 1+2^-53, the least subnormal and DBL_MAX
static const char *dins[] = {
  "0x1.8p1", "0X1P-1074", "0x1p-1075", "0x1.0000000000001p-1075", "0x1.fffffffffffff8p1023",
  "0x1.fffffffffffff7ffp1023", "0x1p", "0x", "-0x0p0", "0x1.23456789abcdef0123p0",
  "0x1.00000000000008p0", "0x0.0000000000001p-1022", "infinity", "-InFiNiT", "nan(abc_123)",
  "nan(a b)", "-nan", " \t\n\v\f\r1.5", "+.5e+1", "-.e1",
  "1e+400", "-1e-400", "2.2250738585072011e-308", "2.4703282292062328e-324", "1.7976931348623158079e308",
  "1.797693134862315808e308", "9007199254740993", "9007199254740993.0000000000000000000001", "1e23",
  "1.00000000000000011102230246251565404236316680908203125",
  "1.00000000000000011102230246251565404236316680908203125000000001", "0e", "1e5x"};
int t_strtod(int k) {
  char *end;
  double d = strtod(dins[k], &end);
  return (int)(end - dins[k]) * 1000000 + fp_id(d);
}

// 2^-1075 exactly (752 digits: a tie between 0 and the least subnormal,
// rounds to even 0), the same with one more digit (above the tie), and a 1
// followed by 400 zeros scaled by e-400 (exactly 1)
#define POW2M1075                                                                \
  "2.4703282292062327208828439643411068618252990130716238221279284125033775"     \
  "363510437593264991818081799618989828234772285886546332835517796989819938"     \
  "739800539093906315035659515570226392290858392449105184435931802849936536"     \
  "152500319370457678249219365623669863658480757001585769269903706311928279"     \
  "558551332927834338409351978015531246597263579574622766465272827220056374"     \
  "006485499977096599470454020828166226237857393450736339007967761930577506"     \
  "740176324673600968951340535537458516661134223766678604162159680461914467"     \
  "291840300530057530849048765391711386591646239524912623653881879636239373"     \
  "280423891018672348497668235089863388587925628302755995657524455507255189"     \
  "313690836254779186948667994968324049705821028513185451396213837722826145"     \
  "437693412532098591327667236328125"
int t_strtod_long(int k) {
  static const char *tie = POW2M1075 "e-324";
  static const char *above = POW2M1075 "1e-324";
  char buf[420];
  const char *s = k == 0 ? tie : above;
  if (k == 2) {
    buf[0] = '1';
    for (int i = 1; i <= 400; ++i) buf[i] = '0';
    strcpy(buf + 401, "e-400");
    s = buf;
  }
  char *end;
  double d = strtod(s, &end);
  return (int)(end - s) * 1000000 + fp_id(d);
}

// strtof rounds once, to binary32 (no double rounding through binary64):
// ties at 1+2^-24 and 2^-150 go to even, digits past the tie decide; the
// overflow threshold is the midpoint between FLT_MAX and 2^128
static const char *fins[] = {
  "1.000000059604644775390625", "1.0000000596046447753906250001", "3.4028235677973366e38",
  "3.40282356779733661637539395458142568448e38",
  "7.00649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625e-46",
  "7.006492321624085354618647916449580656401309709382578858785341419448955413429303007433190941810607910156251e-46",
  "16777217", "0x1.000001p0", "-0x1.8p-150"};
int t_strtof(int k) {
  char *end;
  float f = strtof(fins[k], &end);
  return (int)(end - fins[k]) * 1000000 + fp_id((double)f);
}

// 7.22.1.4: base 0 takes 0x (hex) and 0 (octal) prefixes; a prefix without
// digits leaves the subject "0"; letters are digits up to the base; no
// subject sequence stores nptr itself, even after white space or a sign; out
// of range values saturate and the whole subject is consumed
struct SB {
  const char *s;
  int base;
};
static const SB lins[] = {
  {"  -123abc", 10}, {"0x1F", 0}, {"010", 0}, {"0x", 16}, {"0xz", 0}, {"09", 0},
  {"zZ", 36}, {"1012", 2}, {"  +", 10}, {"9223372036854775807", 10},
  {"9223372036854775808", 10}, {"-9223372036854775808", 10}, {"-9223372036854775809", 10},
  {"99999999999999999999999", 10}, {" \t\n\v\f\r+7", 10}, {"-0x10", 16}, {"Z", 35},
  {"0b101", 0}, {"0b101", 2}};
int t_strtol(int k) {
  char *end;
  long v = strtol(lins[k].s, &end, lins[k].base);
  return (int)(end - lins[k].s) * 10000000 + fold((unsigned long)v);
}

// strtoul negates in the unsigned type ("-1" is ULONG_MAX, no range error);
// a value beyond ULONG_MAX, also after the minus sign, gives ULONG_MAX
static const SB uins[] = {
  {"-1", 10}, {"18446744073709551616", 10}, {"-18446744073709551615", 10},
  {"-18446744073709551616", 10}, {"  +0xFFFFFFFFFFFFFFFF", 0}};
int t_strtoul(int k) {
  char *end;
  unsigned long v = strtoul(uins[k].s, &end, uins[k].base);
  return (int)(end - uins[k].s) * 10000000 + fold(v);
}

// strtoll, strtoull, and atoi/atol/atoll (7.22.1.2: as strtol(nptr, NULL,
// 10) for values in range)
int t_ll(int k) {
  char *end = 0;
  const char *s = "";
  unsigned long long v = 0;
  switch (k) {
  case 0: s = "-9223372036854775808"; v = (unsigned long long)strtoll(s, &end, 10); break;
  case 1: s = "-1"; v = strtoull(s, &end, 10); break;
  case 2: s = "0777"; v = strtoull(s, &end, 0); break;
  case 3: return fold((unsigned long long)(long long)atoi("  -42xyz"));
  case 4: return fold((unsigned long long)atol("-9223372036854775808"));
  case 5: return fold((unsigned long long)atoll("123456789012"));
  }
  return (int)(end - s) * 10000000 + fold(v);
}

// strtold: x86-64 long double has a 64-bit significand (1 + 1e-19 rounds to
// 1 + 2^-63) and a range past 1e4000
int t_strtold(int k) {
  char *end;
  const char *s = k == 0 ? "1.0000000000000000001" : "1e4000";
  long double x = strtold(s, &end);
  int ok = k == 0 ? x > 1.0L : x - x == 0.0L;
  return (int)(end - s) * 10 + ok;
}

// endptr may be a null pointer (7.22.1.3p7, 7.22.1.4p7); atof(nptr) is
// strtod(nptr, NULL) (7.22.1.1)
int t_nullend(int k) {
  if (k == 0) return fp_id(atof("  -0x1.8p4z"));
  if (k == 1) return fp_id(strtod("2.5xyz", (char **)0));
  return (int)strtol("12abc", (char **)0, 10);
}

// "-nan" is negated (7.22.1.3p5): a NaN with the sign bit set
int t_nansign(int k) {
  char *end;
  const char *s = "-nan";
  int neg = k == 0 ? __builtin_signbit(strtod(s, &end)) != 0 : __builtin_signbit(strtof(s, &end)) != 0;
  return (int)(end - s) * 10 + neg;
}

// errno (7.22.1.3p10, 7.22.1.4p8): ERANGE on overflow; whether underflow
// sets it is implementation-defined (glibc: ERANGE); an in-range result
// leaves errno alone, and no library function sets it to zero (7.5p3)
int t_errno(int k) {
  char *end;
  errno = k == 7 ? EDOM : 0;
  switch (k) {
  case 0: strtod("1e400", &end); break;
  case 1: strtod("1e-400", &end); break;
  case 2: strtod("1.5", &end); break;
  case 3: strtof("1e39", &end); break;
  case 4: strtol("9223372036854775808", &end, 10); break;
  case 5: strtoul("18446744073709551616", &end, 10); break;
  case 6: strtoul("-1", &end, 10); break;
  case 7: strtol("123", &end, 10); break;
  }
  int e = errno;
  return e == 0 ? 0 : e == ERANGE ? 1 : e == EDOM ? 2 : 3;
}

// undefined behaviour, not expected to match: 0, 1 strtol with base 1 and 37
// (7.22.1.4p3-5 define bases 0 and 2..36 only; 4p2: undefined by omission);
// 2 atoi of a value int cannot represent (7.22.1.2p1); 3 strtod of a char
// array without a terminator (7.1.4p1: not a string)
int ub_strconv(int k) {
  char *end = 0;
  const char *s = "10";
  long v = -1;
  switch (k) {
  case 0: v = strtol(s, &end, 1); break;
  case 1: v = strtol(s, &end, 37); break;
  case 2: return atoi("2147483648") % 1000;
  case 3: {
    char a[3] = {'1', '2', '3'};
    return fp_id(strtod(a, &end)) % 1000;
  }
  }
  return (end == s) * 1000 + (int)(v % 1000);
}
