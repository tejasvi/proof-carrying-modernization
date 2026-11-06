// strtol, strtoul, strtoll, strtoull under their C11 names (C11 7.22.1.4).
// They are declared here, not through <cstdlib>: glibc 2.38+ headers rename
// them to the C23 functions __isoc23_strtol etc. under _GNU_SOURCE, which g++
// and clang++ define (strconv.cpp tests those). C11 has no 0b prefix, so
// "0b101" is the subject "0". This file includes no header, since <cstdlib>
// or <cmath> would bring the renaming back.
extern "C" long strtol(const char *, char **, int);
extern "C" unsigned long strtoul(const char *, char **, int);
extern "C" long long strtoll(const char *, char **, int);
extern "C" unsigned long long strtoull(const char *, char **, int);

static int fold(unsigned long long u) { return (int)(u % 9999991ull); }

struct SB {
  const char *s;
  int base;
};
static const SB ins[] = {{"0b101", 0},  {"0b101", 2}, {"  -0x1F", 0}, {"0777", 0}, {"9223372036854775808", 10},
                         {"-9223372036854775809", 10}, {"Zz", 36}, {"  +", 10}};
int t_strtol11(int k) {
  char *end;
  long v = strtol(ins[k].s, &end, ins[k].base);
  return (int)(end - ins[k].s) * 10000000 + fold((unsigned long)v);
}

int t_strtoul11(int k) {
  static const char *s[] = {"-1", "18446744073709551616", "0x"};
  char *end;
  unsigned long v = strtoul(s[k], &end, k == 2 ? 16 : 10);
  return (int)(end - s[k]) * 10000000 + fold(v);
}

int t_strtoll11(int k) {
  char *end;
  if (k < 2) {
    const char *s = k == 0 ? "-9223372036854775808" : "0b11";
    long long v = strtoll(s, &end, k == 0 ? 10 : 2);
    return (int)(end - s) * 10000000 + fold((unsigned long long)v);
  }
  const char *s = "0x1p3";
  unsigned long long v = strtoull(s, &end, 0);
  return (int)(end - s) * 10000000 + fold(v);
}
