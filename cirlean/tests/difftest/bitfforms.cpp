// Bit-field forms kept apart from bitfields.cpp (run with CASES=bitfields_cases.txt), so
// that a parser without them still reads that file: volatile accesses
// (`cir.get_bitfield` / `cir.set_bitfield` with `{is_volatile}`) and a zero-width
// bit-field (an `empty` member `!cir.bitfield<[...]>`, no storage, and no
// constant in `#cir.const_record`).
struct __attribute__((packed)) P3 { unsigned a : 3; unsigned b : 13; unsigned c : 20; };   // u16, u8 x 3
struct S8 { unsigned a : 4; unsigned b : 4; };                                              // u8
struct ZW { unsigned a : 4; unsigned : 0; unsigned b : 20; char c; };                        // u8, pad, empty, u8 x 3

// volatile accesses to a 3-byte unit and a 2-byte unit
int t_volatile(int n) {
  volatile P3 p;
  p.c = n;
  p.a = 1;
  p.b = 2;
  return (int)p.c + (int)p.a + (int)p.b;
}

// volatile accesses to a 1-byte unit
int t_volatile_unit(int n) {
  volatile S8 s;
  s.a = n;
  s.b = n + 1;
  return (int)s.a * 16 + (int)s.b;
}

// a zero-width bit-field: the next field starts a new unit; constant and zero initializers
ZW g_zw = {3, 77, 'q'};
ZW g_zw0;
int t_zero_width(int n) {
  ZW z = {1, 2, 'c'};
  z.b += n;
  g_zw0.a = n;
  return (int)z.a + (int)z.b * 10 + z.c + (int)g_zw.b * 1000 + g_zw.c + (int)g_zw0.a + (int)g_zw0.b;
}
