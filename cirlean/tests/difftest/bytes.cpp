// Bytes of objects (run with CASES=bytes_cases.txt): an access through a
// character type reads and writes the bytes of an object's representation
// (C11 6.5p7, last bullet; 6.2.6.1p4), little-endian on our x86-64 targets; and
// pointer arithmetic counts objects of the pointer's type (C11 6.5.6p8), so a
// stride through a char * or short * into an int array, cast back to int *,
// reaches the right element. Expected result (labelled per case in the cases
// file): MATCH on the b_* and s_* cases, UB from cirrun on the u_* controls and
// on the g_* gap (native runs print the GCC result); the d_* cases (the evidence-owner session's probe)
// MATCH but for d_int_over_struct and d_wide_over_char.
#include <cstdlib>

// little-endian: the first byte of 1
int b_endian(int a) {
  int one = 1;
  return *(unsigned char *)&one + a;
}

// byte k of an int
int b_int_bytes(int x, int k) {
  int v = x;
  unsigned char *p = (unsigned char *)&v;
  return p[k];
}

// byte k of a short
int b_short_bytes(int x, int k) {
  short s = (short)x;
  return ((unsigned char *)&s)[k];
}

// byte k of a long long
int b_ll_bytes(int x, int k) {
  long long v = (long long)x * 1000003;
  return ((unsigned char *)&v)[k];
}

// byte k of a double
int b_double_bytes(int x, int k) {
  double d = x / 4.0;
  return ((unsigned char *)&d)[k];
}

// byte k of a float
int b_float_bytes(int x, int k) {
  float f = x / 4.0f;
  return ((unsigned char *)&f)[k];
}

// the byte of a bool
int b_bool_byte(int x) {
  bool b = x != 0;
  return *(unsigned char *)&b;
}

// the bytes of an int swapped in place
int b_write_swap(int x) {
  int v = x;
  unsigned char *p = (unsigned char *)&v;
  unsigned char t = p[0];
  p[0] = p[3];
  p[3] = t;
  t = p[1];
  p[1] = p[2];
  p[2] = t;
  return v;
}

// byte 3 of an int written
int b_write_byte3(int x) {
  int v = x;
  ((unsigned char *)&v)[3] = 0x7f;
  return v;
}

// a char-wise copy between two ints (the destination initialized)
int b_copy_loop(int x) {
  int src = x, dst = 0;
  unsigned char *s = (unsigned char *)&src, *d = (unsigned char *)&dst;
  for (int i = 0; i < 4; i++) d[i] = s[i];
  return dst;
}

// FNV-1a over the bytes of an int array
int b_fnv(int n) {
  int a[4] = {n, n + 1, n * 7, -n};
  unsigned h = 2166136261u;
  const unsigned char *p = (const unsigned char *)a;
  for (int i = 0; i < 16; i++) {
    h ^= p[i];
    h *= 16777619u;
  }
  return (int)(h % 1000003u);
}

// byte k of an int array, across its elements
int b_cross_elem(int k) {
  int a[2] = {0x04030201, 0x08070605};
  return ((unsigned char *)a)[k];
}

// char pointers into an int array: difference and comparison in bytes
int b_ptr_diff(int k) {
  int a[3] = {0, 0, 0};
  unsigned char *p = (unsigned char *)a;
  unsigned char *q = (unsigned char *)(a + 2);
  return (int)(q - p) * 10 + (p + k < q);
}

// the bytes of a struct's int member
int b_member_bytes(int x) {
  struct { char c; int i; } s = {1, x};
  unsigned char *p = (unsigned char *)&s.i;
  return p[0] + p[1] * 256 + s.c * 100000;
}

// a char * stride into an int array, cast back to int *
int s_char_stride(int k) {
  int a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  return *(int *)((char *)a + 4 * k);
}

// a short * stride into an int array, cast back to int *
int s_short_stride(int k) {
  int a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  return *(int *)((short *)a + 2 * k);
}

// a short * walk over an int array, each step read back as int
int s_short_walk(int n) {
  int a[4] = {1, 2, 3, 4};
  short *p = (short *)a;
  int s = 0;
  for (int i = 0; i < 4; i++) s += *(int *)(p + 2 * i);
  return s * n;
}

struct S { int a; int b; };

// an allocator idiom: struct pointers at char offsets into an array of structs
int s_struct_offsets(int k) {
  struct S pool[4] = {{1, 2}, {3, 4}, {5, 6}, {7, 8}};
  char *base = (char *)pool;
  struct S *p = (struct S *)(base + k * sizeof(struct S));
  return p->a * 10 + p->b;
}

// the same on the heap: a pool typed by its first cast, slots at char offsets
int s_heap_pool(int k) {
  struct S *pool = (struct S *)malloc(4 * sizeof(struct S));
  for (int i = 0; i < 4; i++) { pool[i].a = i; pool[i].b = 10 * i; }
  char *base = (char *)pool;
  struct S *p = (struct S *)(base + k * sizeof(struct S));
  int r = p->a + p->b;
  free(pool);
  return r;
}

// a struct * stride over a char buffer (an arena handing out slots): the
// stride moves k * sizeof(struct S) chars; the slot is written through char *
// and read back from the buffer, and the differences count structs and chars
int s_arena_stride(int k) {
  alignas(struct S) char arena[4 * sizeof(struct S)] = {};
  struct S *p = (struct S *)arena;
  struct S *q = p + k;
  char *c = (char *)q;
  c[0] = 7;
  c[1] = 9;
  int off = k * (int)sizeof(struct S);
  return arena[off] * 100 + arena[off + 1] * 10 + (int)(q - p) * 1000 + (int)(c - arena);
}

// a difference of short pointers into an int array
int s_ptrdiff_short(int k) {
  int a[4] = {0, 0, 0, 0};
  short *p = (short *)a;
  short *q = (short *)(a + 3);
  return (int)(q - p) + k;
}

// control: an int access at a misaligned char offset of an int array
int u_misaligned(int k) {
  int a[2] = {1, 2};
  int *p = (int *)((char *)a + 2);
  return *p + k;
}

// control: the bytes of a pointer
int u_ptr_bytes(int x) {
  int v = x;
  int *ptr = &v;
  unsigned char *p = (unsigned char *)&ptr;
  return p[0] & 0;
}

// control: the bytes of a NaN
int u_nan_bytes(int x) {
  double z = x - x;
  double d = z / z;
  return ((unsigned char *)&d)[7];
}

// control: a byte written into an uninitialized int (its other bytes stay indeterminate)
int u_uninit_write(int x) {
  int v;
  ((unsigned char *)&v)[0] = (unsigned char)x;
  return v & 0xff;
}

// control: a byte past an int
int u_past_scalar(int x) {
  int v[1] = {x};
  unsigned char *p = (unsigned char *)v;
  return p[4] & 0;
}

// control: a short read of an int (not a character type)
int u_short_read(int x) {
  int v = x;
  return *(short *)&v;
}

// control: a struct member stored into a slot of a char buffer and read back
// (the buffer's objects are chars: an int access to them, C11 6.5p7)
int u_arena_struct(int k) {
  alignas(struct S) char arena[4 * sizeof(struct S)] = {};
  struct S *q = (struct S *)arena + k;
  q->a = 5;
  return q->a;
}

// a gap, labelled UB: structs in heap storage first used through char *. C
// gives allocated storage the effective type of what is stored in it (C11
// 6.5p6), so this is defined; the model types heap storage at its first cast
// (here char), so the struct member store is UB
int g_heap_char_pool(int k) {
  char *pool = (char *)malloc(4 * sizeof(struct S));
  struct S *p = (struct S *)(pool + k * sizeof(struct S));
  p->a = k;
  p->b = 2 * k;
  int r = p->a + p->b;
  free(pool);
  return r;
}

// the evidence-owner session's probe of the stride rule (the d_* cases, each called with k = 1 and
// k = 3): pointer arithmetic where the pointer's type has another size than
// the object it moves over, and same-size controls
struct pt { int x; int y; };

// char stride 4k over an int array, cast back and read (k = 3 was reported
// out of bounds: element units)
int d_char_stride(int k) {
  int a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  return *(int *)((char *)a + 4 * k);
}
int d_short_stride(int k) {
  int a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  return *(int *)((short *)a + 2 * k);
}
// the difference in bytes of two int elements
int d_char_diff(int k) {
  int a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  return (int)((char *)&a[k] - (char *)&a[0]);
}
// an int pointer over an array of two-int records: (int *)s points to s[0].x
// (6.7.2.1p15), which is no array element, so (int *)s + 1 is one past it and
// may not be dereferenced, and (int *)s + 3 is undefined (C11 6.5.6p7, p8, read
// strictly; the address of s[0].y comes from char arithmetic, b_struct_fnv)
int d_int_over_struct(int k) {
  struct pt s[4] = {{0, 1}, {2, 3}, {4, 5}, {6, 7}};
  return *((int *)s + k);
}
// a char pointer over the records: byte 4k is the first byte of s[k / 2].y
int d_char_over_struct(int k) {
  struct pt s[4] = {{0, 1}, {2, 3}, {4, 5}, {6, 7}};
  return (int)*((unsigned char *)s + 4 * k);
}
// control: plain indexing of a malloc'd int array
int d_heap_int_index(int k) {
  int *p = (int *)malloc(8 * sizeof(int));
  if (!p) return -1;
  for (int i = 0; i < 8; i++) p[i] = 10 * i;
  int r = *(p + k);
  free(p);
  return r;
}
// char stride over a malloc'd int array
int d_heap_char_stride(int k) {
  int *p = (int *)malloc(8 * sizeof(int));
  if (!p) return -1;
  for (int i = 0; i < 8; i++) p[i] = 10 * i;
  int r = *(int *)((char *)p + 4 * k);
  free(p);
  return r;
}
// controls: unsigned over int (same size), a plain int stride
int d_same_size(int k) {
  int a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  return (int)*((unsigned *)a + k);
}
int d_plain(int k) {
  int a[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  return *(a + k);
}
// a char buffer read through unsigned short *: the buffer's objects are
// unsigned chars, an unsigned short access to them is undefined (C11 6.5p7)
int d_wide_over_char(int k) {
  unsigned char b[16];
  for (int i = 0; i < 16; i++) b[i] = (unsigned char)i;
  unsigned short *w = (unsigned short *)b;
  return (int)*(w + k);
}

// pointer arithmetic in bytes from record members and whole objects
struct O2 { struct pt in; int z; };

// the byte offset of a member, from the member's and the object's addresses
int s_member_offset(int k) {
  struct pt s = {k, 2 * k};
  return (int)((char *)&s.y - (char *)&s) + k;
}
// container_of: the object from a pointer to its member
int s_container_of(int k) {
  struct O2 o = {{k, 2 * k}, 3 * k};
  int *pz = &o.z;
  struct O2 *q = (struct O2 *)((char *)pz - 8);
  return q->in.x * 100 + q->in.y * 10 + q->z;
}
// one past a standalone int (C11 6.5.6p7: an array of one), its difference
int s_one_past_scalar(int k) {
  int x = k;
  int *e = &x + 1;
  return (int)(e - &x) + (e > &x) * 10 + x * 100;
}
// control: an int walk over an array of records: the second step is one past
// s[0].x, and its dereference is undefined (6.5.6p8, read strictly)
int u_int_walk_struct(int k) {
  struct pt s[4] = {{0, 1}, {2, 3}, {4, 5}, {6, 7}};
  int sum = 0;
  for (int *q = (int *)s; q < (int *)(s + 4); q++) sum = sum * 3 + *q;
  return sum + k;
}
// the bytes of an array of records, FNV-1a through a char pointer
int b_struct_fnv(int k) {
  struct pt s[2] = {{k, 2}, {300, -4}};
  unsigned h = 2166136261u;
  for (unsigned char *p = (unsigned char *)s; p < (unsigned char *)(s + 2); p++) h = (h ^ *p) * 16777619u;
  return (int)(h % 1000003u);
}

// pointer arithmetic for other types than the character types, strictly (C11
// 6.5.6p7, p8): a pointer to an object that is no array element moves within an
// array of one, the object and one past it
struct S2 { int a; int b; };
// control: the dereference one past a member, at the next member's address
int u_member_one_past(int k) {
  struct S2 s = {k, 2};
  return *(&s.a + 1);
}
// control: an int pointer to a structure points to its first member
int u_struct_int_one_past(int k) {
  struct S2 s = {k, 2};
  return *((int *)&s + 1);
}
// control: two past a member
int u_member_plus_two(int k) {
  struct S2 s = {k, 2};
  int *p = &s.a + 2;
  return p != 0;
}
// one past a member and back, and their difference
int s_member_one_past_back(int k) {
  struct S2 s = {k, 2};
  int *e = &s.a + 1;
  return *(e - 1) * 10 + (int)(e - &s.a);
}
// char arithmetic over the complete object: across the rows of a 2D array
int s_char_rows(int k) {
  int m[2][3] = {{1, 2, 3}, {4 + k, 5, 6}};
  return *(int *)((char *)m[0] + 3 * sizeof(int));
}
// control: int arithmetic stays in its row (one past m[0][2])
int u_int_rows(int k) {
  int m[2][3] = {{1, 2, 3}, {4 + k, 5, 6}};
  return *(m[0] + 3);
}
