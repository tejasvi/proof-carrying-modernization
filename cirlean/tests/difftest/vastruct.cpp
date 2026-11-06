// va_arg of structures and other types (CASES=vastruct_cases.txt): a variadic argument keeps the
// type its call site gives it, and va_arg must name that type (C11 7.16.1.1p2): the same type,
// the signed and the unsigned type of one integer when the value fits both, or void * and a
// pointer to a character type. The cases labelled UB break that rule (natively they read some
// value).
#include <cstdarg>

struct S1 { char c; };
struct S4 { int a; };
struct S8 { int a, b; };
struct S8b { int a, b; };   // the layout of S8, another type
struct S12 { int a, b, c; };
struct S16 { long a, b; };
struct S24 { long a, b, c; };
struct SD { double d; int i; };
struct SF { float f, g; };
struct N { S8 inner; char tag; };
struct A3 { int v[3]; };

static int s8_sum(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int s = 0;
  for (int i = 0; i < n; ++i) {
    S8 x = va_arg(ap, S8);
    s = s * 100 + x.a * 10 + x.b;
  }
  va_end(ap);
  return s;
}

// one character per argument: i int, l long, d double, 1/4/8/c/6/x/D/F/N/A the structures
static long mix(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  long r = 0;
  for (const char *p = fmt; *p; ++p) {
    long v = 0;
    switch (*p) {
    case 'i': v = va_arg(ap, int); break;
    case 'l': v = va_arg(ap, long); break;
    case 'd': v = (long)(va_arg(ap, double) * 2); break;
    case '1': v = va_arg(ap, S1).c; break;
    case '4': v = va_arg(ap, S4).a; break;
    case '8': { S8 x = va_arg(ap, S8); v = x.a * 10 + x.b; break; }
    case 'c': { S12 x = va_arg(ap, S12); v = x.a + x.b + x.c; break; }
    case '6': { S16 x = va_arg(ap, S16); v = x.a - x.b; break; }
    case 'x': { S24 x = va_arg(ap, S24); v = x.a + x.b * x.c; break; }
    case 'D': { SD x = va_arg(ap, SD); v = (long)(x.d * 4) + x.i; break; }
    case 'F': { SF x = va_arg(ap, SF); v = (long)((x.f + x.g) * 2); break; }
    case 'N': { N x = va_arg(ap, N); v = x.inner.a + x.inner.b * 2 + x.tag; break; }
    case 'A': { A3 x = va_arg(ap, A3); v = x.v[0] + x.v[1] * x.v[2]; break; }
    }
    r = r * 7 + v;
  }
  va_end(ap);
  return r;
}

int t_s8(int a, int b) {
  S8 x = {a, b}, y = {b, a}, z = {1, 2};
  return s8_sum(3, x, y, z);
}
int t_sizes(int k) {
  S1 s1 = {(char)(k + 1)};
  S4 s4 = {k * 3};
  S12 s12 = {k, 2, 3};
  S16 s16 = {100L * k, 7};
  S24 s24 = {k, 5, 6};
  return (int)mix("14c6x", s1, s4, s12, s16, s24);
}
int t_mixed(int k) {
  S8 x = {k, 4};
  SD d = {1.25, k};
  SF f = {0.5f, 1.25f};
  return (int)(mix("i8dDlF", k, x, 2.5, d, (long)k * 1000, f) % 1000003);
}
int t_nested(int k) {
  N n = {{k, 3}, 'a'};
  A3 a3 = {{k, 2, 5}};
  return (int)mix("NiA", n, -k, a3);
}

// va_copy taken when the next argument is a structure: both lists read it
static int copy_at_struct(int n, ...) {
  va_list ap, aq;
  va_start(ap, n);
  int first = va_arg(ap, int);
  va_copy(aq, ap);
  S12 x = va_arg(ap, S12);
  S12 y = va_arg(aq, S12);
  int after = va_arg(aq, int);
  va_end(aq);
  va_end(ap);
  return first * 10000 + (x.a + x.b + x.c) * 100 + (y.a * y.b * y.c) + after * 1000000;
}
int t_va_copy_struct(int k) {
  S12 s = {k, 2, 3};
  return copy_at_struct(3, 7, s, 4);
}

// long double arguments
static long ld_sum(int n, ...) {
  va_list ap;
  va_start(ap, n);
  long double s = 0;
  for (int i = 0; i < n; ++i) s += va_arg(ap, long double);
  va_end(ap);
  return (long)(s * 4);
}
int t_long_double(int k) { return (int)ld_sum(3, (long double)k, (long double)0.25, (long double)-1.5); }

// allowed: unsigned read of an int that fits; void * read of a char *
static long relaxed(int n, ...) {
  va_list ap;
  va_start(ap, n);
  unsigned u = va_arg(ap, unsigned);
  void *p = va_arg(ap, void *);
  va_end(ap);
  return (long)u * 10 + *(char *)p;
}
int t_unsigned_void(int k) {
  char c = 'x';
  return (int)relaxed(2, k, &c);
}

// UB controls: a structure of another type, int read as long, a negative int read as unsigned,
// int * read as void *
static int read_s12(int n, ...) {
  va_list ap;
  va_start(ap, n);
  S12 x = va_arg(ap, S12);
  va_end(ap);
  return x.a + x.b;
}
static int read_s8b(int n, ...) {
  va_list ap;
  va_start(ap, n);
  S8b x = va_arg(ap, S8b);
  va_end(ap);
  return x.a * 10 + x.b;
}
static long read_long(int n, ...) {
  va_list ap;
  va_start(ap, n);
  long x = va_arg(ap, long);
  va_end(ap);
  return x;
}
static long read_void(int n, ...) {
  va_list ap;
  va_start(ap, n);
  void *p = va_arg(ap, void *);
  va_end(ap);
  return *(int *)p;
}
int t_ub_wrong_struct(int k) {
  S16 x = {k, 2};
  return read_s12(1, x);
}
int t_ub_same_layout(int k) {
  S8 x = {k, 2};
  return read_s8b(1, x);
}
int t_ub_int_as_long(int k) { return (int)read_long(1, k); }
int t_ub_negative_unsigned(int k) { return (int)relaxed(2, -k, "y"); }
int t_ub_int_ptr_as_void(int k) {
  int v = k;
  return (int)read_void(1, &v);
}

// calls through a function pointer: the callee is known only at run time, so the arguments keep
// their values only; ints still read, a structure does not (a gap of cirlean, labelled)
static int isum(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int s = 0;
  for (int i = 0; i < n; ++i) s += va_arg(ap, int);
  va_end(ap);
  return s;
}
static int (*isum_ptr)(int, ...) = isum;
static int (*s8_ptr)(int, ...) = s8_sum;
int t_indirect_int(int a) { return isum_ptr(2, a, 5); }
int t_indirect_struct(int a) {
  S8 x = {a, 1};
  return s8_ptr(1, x);
}
