/* Loops whose variable is a pointer walking a string (`cir_loop` with a
   `T*` binder: the invariant names the element index; Examples/PtrLoop.lean). */
int str_len(const char *s) {
  const char *p = s;
  while (*p != '\0') p++;
  return (int)(p - s);
}

int count_char(const char *s, char c) {
  int n = 0;
  while (*s != '\0') {
    if (*s == c) n++;
    s++;
  }
  return n;
}

/* The increment in the condition of a do-while, as tiny-regex-c's matchcharclass. */
int has_char(char c, const char *str) {
  do {
    if (c == str[0]) return 1;
  } while (*str++ != '\0');
  return 0;
}
