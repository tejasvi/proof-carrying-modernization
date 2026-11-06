// C library: heap allocation, string length, typed memset/memcpy/memcmp.
#include <clocale>
#include <cstdlib>
#include <cstring>

int t_malloc_array(int n) {
  int *a = (int *)malloc(sizeof(int) * 5);
  for (int i = 0; i < 5; ++i) a[i] = i * n;
  int s = a[1] + a[4];
  free(a);
  return s;
}
int t_calloc_zero(int n) {
  int *a = (int *)calloc(4, sizeof(int));
  a[2] = n;
  int s = a[0] + a[1] + a[2] + a[3];
  free(a);
  return s;
}
struct P { int x; int y; };
int t_malloc_struct(int n) {
  P *p = (P *)malloc(sizeof(P));
  p->x = n; p->y = 2 * n;
  int s = p->x + p->y;
  free(p);
  return s;
}
int t_strlen(int n) {
  const char *s = "hello";
  return (int)strlen(s) + n;
}
int t_memset(int n) {
  int a[6];
  memset(a, 0, sizeof(a));
  a[3] = n;
  return a[0] + a[3] + a[5];
}
int t_memcpy(int n) {
  int a[4] = {1, 2, 3, n};
  int b[4];
  memcpy(b, a, sizeof(a));
  return b[0] + b[3];
}
int t_memcmp(int n) {
  char a[3] = {'a', 'b', 'c'};
  char b[3] = {'a', 'b', (char)('c' + n)};
  int r = memcmp(a, b, 3);
  return r < 0 ? -1 : (r > 0 ? 1 : 0);
}

int t_strcmp(int k) {
  const char *a = "apple";
  const char *b = k == 0 ? "apple" : k == 1 ? "apricot" : "app";
  int r = strcmp(a, b);
  return r < 0 ? -1 : r > 0 ? 1 : 0;
}
int t_strncmp(int n) {
  int r = strncmp("token", "tokyo", n);
  return r < 0 ? -1 : r > 0 ? 1 : 0;
}

#include <cstdio>
int t_strtod(int k) {
  const char *s[] = {"12.5", "-3e2", "  0.001x", "abc"};
  char *e;
  double d = strtod(s[k], &e);
  return (int)(d * 1000) + (int)(e - s[k]) * 1000000;
}
int t_sprintf(int x) {
  char buf[32];
  int n = sprintf(buf, "v=%04d|%x|%s", x, x, "ok");
  return n * 1000 + buf[2] + buf[n - 1];
}
int t_strcpy(int k) {
  char buf[8];
  strcpy(buf, k ? "hello" : "");
  return (int)strlen(buf) * 100 + buf[0];
}
int t_realloc(int n) {
  int *p = (int *)malloc(2 * sizeof(int));
  p[0] = 5;
  p[1] = 6;
  p = (int *)realloc(p, n * sizeof(int));
  p[n - 1] = 9;
  int r = p[0] + p[1] + p[n - 1];
  free(p);
  return r;
}
int t_uchar_view(int k) {  // a char object read through unsigned char *
  char s[3] = {(char)k, 'a', 0};
  const unsigned char *u = (const unsigned char *)s;
  return u[0] + u[1];
}

// strchr: the position of (char)c in a fixed string, -1 if absent (the
// terminator is found for c == 0)
int strchr_pos(int c) {
  const char *s = "hello, world";
  const char *p = strchr(s, c);
  return p ? (int)(p - s) : -1;
}

// realloc of single objects: malloc(1) typed char, malloc(sizeof) typed struct
int t_realloc_one(int n) {
  char *p = (char *)malloc(1);
  p[0] = (char)n;
  p = (char *)realloc(p, 8);
  for (int i = 1; i < 8; ++i) p[i] = (char)i;
  int r = p[0] + p[7];
  free(p);
  return r;
}
struct RP { int a; int b; };
int t_realloc_struct(int n) {
  RP *q = (RP *)malloc(sizeof(RP));
  q->a = n;
  q->b = 2 * n;
  q = (RP *)realloc(q, 3 * sizeof(RP));
  q[2].a = 10;
  q[2].b = 20;
  int r = q[0].a + q[0].b + q[2].a + q[2].b;
  free(q);
  return r;
}
// localeconv in the C locale (setlocale never called)
int t_localeconv(int n) {
  struct lconv *l = localeconv();
  return l->decimal_point[0] + (l->decimal_point[1] == 0) + (l->thousands_sep[0] == 0) + n;
}
