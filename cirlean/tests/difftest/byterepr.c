/* Bytes that are no value of the object's type (C11 6.2.6.1p4-5): a _Bool's byte other than 0 or 1, a NaN's bit
   pattern in a double or float, written through a character lvalue or by memcpy / memset byte by byte. The object
   keeps them; only a read of the object as its type is undefined (a _Bool) or not modelled (a NaN). Run with
   CASES=byterepr_cases.txt, which describes the cases. */
#include <string.h>

/* a _Bool's byte set to 2, then back to 0, then the _Bool read (soundness audit F8) */
int r_bool_2_then_0(int k) {
  _Bool b = 1;
  unsigned char *p = (unsigned char *)&b;
  p[0] = (unsigned char)(2 + k);
  p[0] = 0;
  return b + 10;
}
/* the byte read back through the character lvalue while it is 2, then set to 1 and the _Bool read */
int r_bool_byte_read(int k) {
  _Bool b = 1;
  unsigned char *p = (unsigned char *)&b;
  p[0] = (unsigned char)(2 + k);
  int r = p[0];
  p[0] = 1;
  return r * 10 + b;
}
/* the _Bool read while its byte is 2 */
int r_bool_read_2(int k) {
  _Bool b = 0;
  unsigned char *p = (unsigned char *)&b;
  p[0] = (unsigned char)(2 + k);
  return b;
}
/* a structure with such a _Bool member, copied; the copy's byte read */
struct SB { _Bool b; int x; };
int r_bool_struct_copy(int k) {
  struct SB s = {1, 5};
  ((unsigned char *)&s.b)[0] = (unsigned char)(3 + k);
  struct SB t = s;
  return ((unsigned char *)&t.b)[0] * 10 + t.x;
}
/* infinity copied byte by byte, last byte first, into 5e-324: NaN bits for some steps (soundness audit F9) */
int r_transient_nan(int k) {
  double src = 1e308;
  src = src * 10.0;
  double dst = 5e-324;
  unsigned char *s = (unsigned char *)&src, *d = (unsigned char *)&dst;
  for (int i = 7; i >= 0; --i) d[i] = s[i];
  return (dst > 1e308) + k;
}
/* control: the forward copy */
int r_forward_copy(int k) {
  double src = 1e308;
  src = src * 10.0;
  double dst = 5e-324;
  unsigned char *s = (unsigned char *)&src, *d = (unsigned char *)&dst;
  for (int i = 0; i < 8; ++i) d[i] = s[i];
  return (dst > 1e308) + k;
}
/* the same for a float: infinity copied last byte first into the smallest denormal */
int r_float_transient(int k) {
  float src = 3e38f;
  src = src * 10.0f;
  float dst = 1e-45f;
  unsigned char *s = (unsigned char *)&src, *d = (unsigned char *)&dst;
  for (int i = 3; i >= 0; --i) d[i] = s[i];
  return (dst > 3e38f) + k;
}
/* a NaN's bytes written into a double and read back through the character lvalue */
int r_nan_bytes_read(int k) {
  double d = 0.0;
  unsigned char *p = (unsigned char *)&d;
  p[7] = 0x7f;
  p[6] = (unsigned char)(0xf8 + k);
  return p[7] + p[6];
}
/* the double read while it holds a NaN's bits */
int r_nan_double_read(int k) {
  double d = 0.0;
  unsigned char *p = (unsigned char *)&d;
  p[7] = 0x7f;
  p[6] = (unsigned char)(0xf8 + k);
  return d != d;
}
/* byte 2 copied into a _Bool by memcpy, then copied back out into an unsigned char */
int r_memcpy_bool_byte(int k) {
  unsigned char two = (unsigned char)(2 + k), c = 0;
  _Bool b = 1;
  memcpy(&b, &two, 1);
  memcpy(&c, &b, 1);
  return c;
}
/* the _Bool read after byte 2 was copied into it */
int r_memcpy_bool_read(int k) {
  unsigned char two = (unsigned char)(2 + k);
  _Bool b = 0;
  memcpy(&b, &two, 1);
  return b;
}
/* memset of 0xff makes a double's bytes a NaN's; the bytes read back through the character lvalue */
int r_memset_nan_bytes(int k) {
  double d;
  memset(&d, 0xff, sizeof d);
  unsigned char *p = (unsigned char *)&d;
  return p[0] + p[7] + k;
}
/* a NaN's bytes copied into a double, then its two high bytes replaced by those of 1.0: a number again */
int r_memcpy_nan_partial(int k) {
  unsigned char nan[8] = {1, 0, 0, 0, 0, 0, 0xf8, 0x7f};
  unsigned char one[2] = {0xf0, 0x3f};
  double d;
  memcpy(&d, nan, 8);
  memcpy((unsigned char *)&d + 6, one, 2);
  return (d > 1.0 && d < 1.0000001) + k;
}
/* infinity copied into 5e-324 one byte per memcpy, last byte first: NaN bits for some steps */
int r_memcpy_transient(int k) {
  double src = 1e308;
  src = src * 10.0;
  double dst = 5e-324;
  for (int i = 7; i >= 0; --i) memcpy((unsigned char *)&dst + i, (unsigned char *)&src + i, 1);
  return (dst > 1e308) + k;
}
/* control: a double holding a NaN's bytes copied whole by memcpy (as a value); a byte of the copy read */
int r_memcpy_raw_whole(int k) {
  double d = 0.0, e = 2.0;
  unsigned char *p = (unsigned char *)&d;
  p[7] = 0x7f;
  p[6] = (unsigned char)(0xf8 + k);
  memcpy(&e, &d, sizeof d);
  return ((unsigned char *)&e)[7];
}
