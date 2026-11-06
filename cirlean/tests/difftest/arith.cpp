// Arithmetic, conversions and comparisons.
int t_arith_mix(int a, int b) {
  int s = a * 3 - b;
  s = s + (a / 2) - (b % 5);
  if (a > b) s += 7; else s -= 7;
  return s;
}

int t_div_neg(int a, int b) {
  if (b == 0) return 0;
  return (a / b) * 100 + (a % b);
}

int t_unsigned_wrap(int a) {
  unsigned u = (unsigned)a;
  u = u * 2654435761u;
  return (int)(u >> 16);
}

int t_bits(int a, int b) {
  return ((a & b) | (a ^ 0x5A)) + ((b << 2) >> 1) + (~a & 0xFF);
}

int t_char_short(int a) {
  char c = (char)a;
  short s = (short)(a * 1000);
  unsigned char uc = (unsigned char)a;
  return c + s + uc;
}

int t_ternary_chain(int a) {
  return a < 0 ? -1 : a == 0 ? 0 : a < 10 ? 1 : 2;
}

int t_bool_logic(int a, int b) {
  bool x = a > 0 && b > 0;
  bool y = a < 0 || b < 0;
  bool z = !(a == b);
  return x * 4 + y * 2 + z;
}

long long t_wide(int a, int b) {
  long long p = (long long)a * (long long)b;
  return p / 7 + (p % 1000);
}

int t_wide_int(int a, int b) { return (int)(t_wide(a, b) % 100000); }
