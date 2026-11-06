/* Union reads in C (run with CASES=unionact_cases.txt, next to unionact.cpp): reading another member
   reinterprets the stored bytes (C11 6.5.2.3p3, footnote 95; 6.5p7), also for a member of another size: each
   of its scalars is composed from the active member's bytes (little-endian). A byte the active member does not
   hold is indeterminate, a trap representation undefined, a NaN pattern not modelled (UB from cirrun). From
   the soundness audit of next3 709db2e (NX2) plus controls. Members of the same size: a _Bool and an unsigned
   char read each other's byte, and the bytes that a _Bool or float member keeps after a character store (a trap
   byte, a NaN pattern) are read through an integer member as they are. */
union IC { int i; unsigned char c[4]; };
union SC { short s[2]; int i; };
union LI { long long ll; int i[2]; };
union FC { unsigned char c[4]; float f; };
union IB { int i; _Bool b; };
union CI { unsigned char c; int i; };
union BC { _Bool b; unsigned char c; };
union FI { float f; unsigned int i; };

/* NX2: byte 1 of the int through the char array member */
int c_char_member(int k) { union IC u; u.i = 0x01020304 + k; return u.c[1]; }

/* control: the same byte through a char pointer to the union */
int c_char_pointer(int k) { union IC u; u.i = 0x01020304 + k; unsigned char *p = (unsigned char *)&u; return p[1]; }

/* NX2: a byte stored through the char array member, then the int read */
int c_char_member_store(int k) { union IC u; u.i = 0x01020304; u.c[0] = (unsigned char)(0x10 + k); return u.i; }

/* NX2: the halves of an int through a short array member */
int c_short_halves(int k) { union SC u; u.i = 0x00020001 + k; return u.s[0] * 10 + u.s[1]; }

/* NX2: the halves of a long long through an int array member */
int c_ll_halves(int k) { union LI u; u.ll = 0x0000000200000001LL + k; return u.i[0] * 10 + u.i[1]; }

/* a float composed from bytes stored through the char array member */
int c_float_from_bytes(int k) {
  union FC u;
  u.c[0] = 0; u.c[1] = 0; u.c[2] = 0x80; u.c[3] = (unsigned char)(0x3f + k);
  return (int)(u.f * 10);
}

/* a _Bool read from an int's first byte, 1 */
int c_bool_from_int(int k) { union IB u; u.i = 1 + k; return u.b; }

/* control: a _Bool from a byte 2, a trap representation (6.2.6.1p5) */
int c_bool_trap_from_int(int k) { union IB u; u.i = 2 + k; return u.b; }

/* control: an int read after a char store, its other bytes unspecified (6.2.6.1p7) */
int c_larger_member(int k) { union CI u; u.c = (unsigned char)(5 + k); return u.i; }

/* control: a NaN pattern composed from bytes (not modelled) */
int c_nan_from_bytes(int k) {
  union FC u;
  u.c[0] = (unsigned char)(1 + k); u.c[1] = 0; u.c[2] = 0xc0; u.c[3] = 0x7f;
  return u.f != u.f;
}

/* a _Bool read through an unsigned char member, 1 */
int c_bool_to_char(int k) { union BC u; u.b = 1 + k; return u.c; }

/* an unsigned char 1 read through a _Bool member */
int c_char_to_bool(int k) { union BC u; u.c = (unsigned char)(1 + k); return u.b; }

/* control: an unsigned char 2 read through a _Bool member, a trap representation (6.2.6.1p5) */
int c_char_to_bool_trap(int k) { union BC u; u.c = (unsigned char)(2 + k); return u.b; }

/* a byte 2 stored into the _Bool member through a char pointer, read through the unsigned char member */
int c_bool_byte_as_char(int k) {
  union BC u; u.b = 0;
  unsigned char *p = (unsigned char *)&u.b;
  *p = (unsigned char)(2 + k);
  return u.c;
}

/* a NaN pattern stored into the float member through a char pointer, read through the int member */
int c_nan_bytes_as_int(int k) {
  union FI u; u.f = 1.0f;
  unsigned char *p = (unsigned char *)&u.f;
  p[2] = (unsigned char)(0xc0 + k); p[3] = 0x7f;
  return (int)(u.i >> 16);
}
