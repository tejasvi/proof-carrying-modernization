// Type-punning regressions (run with CASES=punning_cases.txt): musl-style word
// loops that read and write char arrays through a word type declared
// __attribute__((__may_alias__)), as musl's strlen and memcpy do under
// __GNUC__. GCC defines these accesses; in standard C they are undefined, and
// so is a type-punned scalar access in the semantics (2d65713). Expected
// result: cirrun reports UB "type-punned access" on every case (the difftest
// prints UB); native runs print the GCC result.
#include <cstddef>

typedef unsigned long __attribute__((__may_alias__)) word;

#define ONES ((unsigned long)-1 / 255)
#define HIGHS (ONES * 128)
#define HASZERO(x) (((x) - ONES) & ~(x) & HIGHS)

// strlen's word loop: whole words while none has a zero byte, then bytes
int t_word_strlen(int n) {
  alignas(8) char buf[64];
  if (n < 0 || n > 60) return -1;
  for (int i = 0; i < 64; i++) buf[i] = i < n ? 'a' : 0;
  const char *s = buf;
  const word *w = (const word *)s;
  while (!HASZERO(*w)) w++;
  s = (const char *)w;
  while (*s) s++;
  return (int)(s - buf);
}

// memcpy's word path: aligned char arrays copied a word at a time
int t_word_memcpy(int n) {
  alignas(8) unsigned char src[32], dst[32];
  for (int i = 0; i < 32; i++) { src[i] = (unsigned char)(i * 7 + n); dst[i] = 0; }
  word *d = (word *)dst;
  const word *s = (const word *)src;
  for (int i = 0; i < 4; i++) d[i] = s[i];
  int sum = 0;
  for (int i = 0; i < 32; i++) sum += dst[i];
  return sum;
}
