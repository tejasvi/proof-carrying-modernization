// Type punning on record members (run with CASES=recpun_cases.txt): a scalar
// access to a struct member through a pointer of another scalar type, plain,
// volatile or atomic (load, store, read-modify-write). As for
// array elements (2d65713), memory holds typed members, not bytes: an access
// whose type does not match the member's declared type (same-width integers of
// either signedness, any pointers and the same float kind match) is undefined,
// "type-punned access". A character access is not punned: it reads or writes a
// byte of the member (bytes.cpp), so the two char stores below are defined.
// Expected result (labelled per case in the cases file): UB from cirrun on the
// other r_pun_* cases (native runs print the GCC result), MATCH on the char
// stores and the r_ok_* controls.

struct SI { int i; int j; };
struct Cnt { int use; int weak; };
struct SF { float f; int n; };
struct SC { char c; int x; };
struct SP { int *p; int n; };
struct Q { int arr[2]; };
struct R { int k; Q q; };
union UF { float f; unsigned u; };

// a char store into an int member: its byte 0
int r_pun_char_into_int(int v) {
  SI s = {v, 0};
  *(char *)&s.i = 7;
  return s.i;
}

// a long long read over two int members (libstdc++'s shared_ptr counters,
// _M_use_count and _M_weak_count read at once)
int r_pun_ll_over_ints(int a, int b) {
  Cnt c = {a, b};
  long long x = *(long long *)&c.use;
  return (int)(x % 1000003);
}

// an unsigned read of a float member
int r_pun_unsigned_of_float(int v) {
  SF s = {(float)v, 0};
  unsigned u = *(unsigned *)&s.f;
  return (int)(u % 1000003u);
}

// the same read as an atomic load: libstdc++'s _Sp_counted_base::_M_release
// loads _M_use_count and _M_weak_count at once with
// __atomic_load_n((long long *)&_M_use_count, __ATOMIC_ACQUIRE)
int r_pun_atomic_ll_over_ints(int a, int b) {
  Cnt c = {a, b};
  long long x = __atomic_load_n((long long *)&c.use, __ATOMIC_ACQUIRE);
  return (int)(x % 1000003);
}

// a volatile long long read over two int members
int r_pun_volatile_ll_over_ints(int a, int b) {
  Cnt c = {a, b};
  long long x = *(volatile long long *)&c.use;
  return (int)(x % 1000003);
}

// an atomic long long store over two int members
int r_pun_atomic_store_ll(int a, int b) {
  Cnt c = {0, 0};
  __atomic_store_n((long long *)&c.use, ((long long)b << 32) | (unsigned)a, __ATOMIC_RELEASE);
  return c.use * 10 + c.weak;
}

// an atomic read-modify-write of a long long over two int members
int r_pun_atomic_fetch_add_ll(int a, int b) {
  Cnt c = {a, b};
  long long old = __atomic_fetch_add((long long *)&c.use, 1, __ATOMIC_ACQ_REL);
  return (int)(old % 1000003) + c.use;
}

// a char store into an int element of an array member of a nested struct: its
// byte 0
int r_pun_char_into_nested(int v) {
  R r = {0, {{v, v}}};
  *(char *)&r.q.arr[1] = 1;
  return r.q.arr[1];
}

// control: an unsigned read of an int member (same width, either signedness)
int r_ok_unsigned_of_int(int v) {
  SI s = {v, 1};
  return (int)(*(unsigned *)&s.i % 1000003u);
}

// control: an atomic load of an int member with its own type
int r_ok_atomic_int_member(int a, int b) {
  Cnt c = {a, b};
  return __atomic_load_n(&c.use, __ATOMIC_ACQUIRE) * 10 + c.weak;
}

// control: an atomic read-modify-write of an int member with its own type
int r_ok_atomic_fetch_add_int(int a, int b) {
  Cnt c = {a, b};
  int old = __atomic_fetch_add(&c.use, 5, __ATOMIC_ACQ_REL);
  return old * 100 + c.use * 10 + c.weak;
}

// control: a char member through unsigned char *
int r_ok_char_member_uchar(int v) {
  SC s = {(char)v, 9};
  return *(unsigned char *)&s.c;
}

// control: a pointer member through another pointer type
int r_ok_ptr_member_other(int v) {
  int z = v;
  SP s = {&z, 0};
  void *q = *(void **)&s.p;
  return *(int *)q + (q == (void *)&z);
}

// control: a whole-struct copy
int r_ok_struct_copy(int a, int b) {
  SI s = {a, b};
  SI t = s;
  t.j += 1;
  return s.i * 10 + t.j;
}

// control: a member of an array of structs, written and read with its type
int r_ok_array_of_structs(int v) {
  SI a[3] = {};
  a[1].j = v;
  return a[1].j + a[0].i;
}

// control: a union read of another member of the same size (unionpun's
// reinterpretation, through the member's own pointer)
int r_ok_union_member(int v) {
  UF x;
  x.f = (float)v;
  return (int)(x.u % 1000003u);
}
