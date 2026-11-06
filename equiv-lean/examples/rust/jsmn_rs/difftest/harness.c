/* Differential driver for jsmn.h @ 25647e6 (default configuration): reads cases (u32 num_tokens, u32 len, len
 * bytes; little endian) and prints, per case, jsmn_parse's return value and the first min(max(ret, 0), num_tokens)
 * tokens as type:start:end:size. */
#define JSMN_STATIC
#include "jsmn.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb");
  uint32_t n, len;
  if (!f) return 2;
  while (fread(&n, 4, 1, f) == 1 && fread(&len, 4, 1, f) == 1) {
    char *js = malloc(len + 1);
    jsmntok_t *toks = calloc(n ? n : 1, sizeof(jsmntok_t));
    jsmn_parser p;
    int r, k, i;
    if (fread(js, 1, len, f) != len) return 3;
    jsmn_init(&p);
    r = jsmn_parse(&p, js, len, toks, n);
    printf("%d", r);
    k = r < 0 ? 0 : (r < (int)n ? r : (int)n);
    for (i = 0; i < k; i++)
      printf(" %d:%d:%d:%d", (int)toks[i].type, toks[i].start, toks[i].end, toks[i].size);
    printf("\n");
    free(js);
    free(toks);
  }
  fclose(f);
  return 0;
}
