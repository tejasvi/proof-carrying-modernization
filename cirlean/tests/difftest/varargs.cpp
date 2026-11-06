// Variadic functions: va_start / va_arg / va_end (cir.va_*).
#include <cstdarg>

static int sum(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int s = 0;
  for (int i = 0; i < n; ++i)
    s += va_arg(ap, int);
  va_end(ap);
  return s;
}

static int check(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = 0;
  for (const char *p = fmt; *p; ++p) {
    if (*p == 'i')
      r += va_arg(ap, int);
    else if (*p == 's') {
      const char *s = va_arg(ap, const char *);
      while (*s++)
        r += 100;
    }
  }
  va_end(ap);
  return r;
}

int t_va_sum(int a, int b) { return sum(3, a, b, a * b); }
int t_va_none(int a) { return sum(0) + a; }
int t_va_check(int a) { return check("isi", a, "abc", 7); }
