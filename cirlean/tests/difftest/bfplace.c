/* A structure with bit-fields placed over other objects (C11 6.5p7): a bit-field lvalue has its declared type
   (unsigned int, int, ...), whatever storage unit the compiler gives it (Clang: one byte for struct {unsigned a:4,
   b:4;}, two for 4 + 8 bits); the access touches only the unit's bytes. Run with CASES=bfplace_cases.txt, which
   describes the cases. */
#include <string.h>

struct BF8 { unsigned a : 4, b : 4; };
struct BF12 { unsigned a : 4, b : 8; };
struct BF24 { unsigned a : 4, b : 20; };
struct BF32 { unsigned a : 16, b : 16; };
struct BFI { int a : 4, b : 4; };
struct BFB { _Bool f : 1; };
struct BFC { unsigned char c : 4; };

/* unsigned int bit-fields in one byte over an unsigned int */
int p_bf8_over_unsigned(int k) {
  unsigned u = 0x00000053u + k;
  struct BF8 *p = (struct BF8 *)&u;
  return (int)(p->a * 10 + p->b);
}
/* the same over a float (soundness audit B1) */
int p_bf8_over_float(int k) {
  float x = 1.0f + k;
  struct BF8 *p = (struct BF8 *)&x;
  return (int)(p->a * 10 + p->b);
}
/* the same over a char array (soundness audit B1) */
int p_bf8_over_chars(int k) {
  char buf[4] = {0x53, 0, 0, 0};
  buf[1] = (char)k;
  struct BF8 *p = (struct BF8 *)buf;
  return (int)(p->a * 10 + p->b);
}
/* a store through such a bit-field over a float (soundness audit B1) */
int p_bf8_store_over_float(int k) {
  float x = 0.0f;
  struct BF8 *p = (struct BF8 *)&x;
  p->a = 1 + k;
  return x != 0.0f;
}
/* 4 + 8 bits (a two-byte unit) over an unsigned int (soundness audit B2) */
int p_bf12_over_unsigned(int k) {
  unsigned u = 0x00000123u + k;
  struct BF12 *p = (struct BF12 *)&u;
  return (int)(p->a * 1000 + p->b);
}
/* a store into the 8-bit field over an unsigned int (soundness audit B2) */
int p_bf12_store_over_unsigned(int k) {
  unsigned u = 0;
  struct BF12 *p = (struct BF12 *)&u;
  p->b = 0xAB + k;
  return (int)u;
}
/* 4 + 20 bits over an unsigned int */
int p_bf24_over_unsigned(int k) {
  unsigned u = 0x00012345u + k;
  struct BF24 *p = (struct BF24 *)&u;
  return (int)(p->a * 1000000 + p->b);
}
/* 16 + 16 bits over an unsigned int */
int p_bf32_over_unsigned(int k) {
  unsigned u = 0x00020001u + k;
  struct BF32 *p = (struct BF32 *)&u;
  return (int)(p->a * 10 + p->b);
}
/* int bit-fields in one byte over an int */
int p_bfi_over_int(int k) {
  int x = 0x00000035 + k;
  struct BFI *p = (struct BFI *)&x;
  return p->a * 10 + p->b;
}
/* 4 + 8 bits over an unsigned short: unsigned int lvalues over an unsigned short object */
int p_bf12_over_ushort(int k) {
  unsigned short s[2] = {0x0123, 0};
  s[1] = (unsigned short)k;
  struct BF12 *p = (struct BF12 *)s;
  return (int)(p->a * 1000 + p->b);
}
/* int bit-fields over a char array */
int p_bfi_over_chars(int k) {
  char buf[4] = {0x35, 0, 0, 0};
  buf[1] = (char)k;
  struct BFI *p = (struct BFI *)buf;
  return p->a * 10 + p->b;
}
/* a _Bool bit-field over a _Bool */
int p_bfb_over_bool(int k) {
  _Bool b = 1;
  struct BFB *p = (struct BFB *)&b;
  return p->f + k;
}
/* an unsigned char bit-field over a float: a character lvalue */
int p_bfc_over_float(int k) {
  float x = 1.0f;
  unsigned char *q = (unsigned char *)&x;
  q[0] = (unsigned char)(0x0b + k);
  struct BFC *p = (struct BFC *)&x;
  return p->c;
}
/* control: the bit-fields of a structure object */
int p_bf12_object(int k) {
  struct BF12 s;
  s.a = 3;
  s.b = 0x12 + k;
  return (int)(s.a * 1000 + s.b);
}
/* control: a structure object's bit-field unit read through its unsigned char bytes */
int p_bf12_bytes(int k) {
  struct BF12 s;
  memset(&s, 0, sizeof s);
  s.a = 3;
  s.b = 0x12 + k;
  return ((unsigned char *)&s)[0] + ((unsigned char *)&s)[1] * 256;
}
