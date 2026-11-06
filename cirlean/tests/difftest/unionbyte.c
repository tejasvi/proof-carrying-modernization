/* Character arithmetic into a union (C11 6.5.6p8, 6.7.2.1p16): a char pointer at a byte where a subobject of the
   union's active member starts, converted back, designates that subobject, as in a structure. Run with
   CASES=unionbyte_cases.txt, which describes the cases. */

union US { int i; short s[2]; };
union UC { char c; int i; };

/* a short pointer at byte 2 of a union whose short array is active: s[1] (soundness audit F10) */
int u_member_char_offset(int k) {
  union US u;
  u.s[0] = 1;
  u.s[1] = (short)(2 + k);
  short *p = (short *)((char *)&u + 2);
  return *p;
}
/* a store through that pointer */
int u_member_store(int k) {
  union US u;
  u.s[0] = 1;
  u.s[1] = 2;
  short *p = (short *)((char *)&u + 2);
  *p = (short)(7 + k);
  return u.s[1];
}
/* the char pointer itself reads byte 2 of s[1] */
int u_member_char_read(int k) {
  union US u;
  u.s[0] = 1;
  u.s[1] = (short)(0x0302 + k);
  return *((unsigned char *)&u + 2);
}
/* the int member active: byte 2 lies inside the int, a short there is half of it */
int u_int_half(int k) {
  union US u;
  u.i = 0x00030001 + k;
  short *p = (short *)((char *)&u + 2);
  return *p;
}
/* a byte past the active member c (C: its value is unspecified, 6.2.6.1p7) */
int u_past_active(int k) {
  union UC u;
  u.i = 0;
  u.c = (char)(1 + k);
  return *((char *)&u + 2);
}
/* the pointer formed while no member holds a value, then s stored, then the pointer read */
int u_formed_before(int k) {
  union US u;
  short *p = (short *)((char *)&u + 2);
  u.s[0] = 1;
  u.s[1] = (short)(5 + k);
  return *p;
}
