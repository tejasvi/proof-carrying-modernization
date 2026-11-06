// atoi, atol, atoll (run with CASES=atoi_cases.txt): strtol's base-10 parse
// (white space, an optional sign, decimal digits; 0 without digits). A value
// the result type cannot represent is undefined (C11 7.22.1.2p1). Expected
// result (labelled per case in the cases file): MATCH in range; UB from
// cirrun out of range (native runs print glibc's result: atoi truncates
// strtol's value, atol and atoll clamp it).
#include <cstdlib>

static const char *const strs[] = {
  "0",                      // 0
  "42",                     // 1
  "-17",                    // 2
  "  +123abc",              // 3
  "\t\n\v\f\r 99",          // 4
  "abc",                    // 5
  "",                       // 6
  "-",                      // 7
  "+-5",                    // 8
  "2147483647",             // 9
  "-2147483648",            // 10
  "2147483648",             // 11
  "-2147483649",            // 12
  "007",                    // 13
  "  -0",                   // 14
  "12 34",                  // 15
  "9223372036854775807",    // 16
  "-9223372036854775808",   // 17
  "9223372036854775808",    // 18
  "-9223372036854775809",   // 19
  "99999999999999999999",   // 20
  "0x1A",                   // 21
  "1e5",                    // 22
};

int t_atoi(int i) { return atoi(strs[i]); }

int t_atol_lo(int i) { return (int)(atol(strs[i]) % 1000000007L); }
int t_atol_hi(int i) { return (int)(atol(strs[i]) / 4294967296L); }

int t_atoll_lo(int i) { return (int)(atoll(strs[i]) % 1000000007LL); }
int t_atoll_hi(int i) { return (int)(atoll(strs[i]) / 4294967296LL); }

int t_atoi_buf(int v) {
  char buf[16];
  char tmp[12];
  int k = 0, m = 0;
  buf[k++] = ' ';
  if (v < 0) { buf[k++] = '-'; v = -v; }
  do { tmp[m++] = (char)('0' + v % 10); v /= 10; } while (v != 0);
  while (m > 0) buf[k++] = tmp[--m];
  buf[k++] = 'x';
  buf[k] = 0;
  return atoi(buf) + 1;
}
