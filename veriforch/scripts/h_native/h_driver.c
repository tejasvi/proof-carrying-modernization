/* Pre-registration H: native driver for one fuzz-harness input. Reads the file named by argv[1] into a heap buffer of
   exactly its size and calls LLVMFuzzerTestOneInput once, as libFuzzer's single-input mode does. Compiled without
   sanitizer flags (Theorem's driver is uninstrumented too). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: %s INPUT\n", argv[0]);
    return 2;
  }
  FILE *f = fopen(argv[1], "rb");
  if (f == NULL) { perror("h_driver: fopen"); return 2; }
  if (fseek(f, 0, SEEK_END) != 0) { perror("h_driver: fseek"); return 2; }
  long n = ftell(f);
  if (n < 0) { perror("h_driver: ftell"); return 2; }
  rewind(f);
  uint8_t *buf = malloc((size_t)n);
  if (buf == NULL && n > 0) { fprintf(stderr, "h_driver: malloc failed\n"); return 2; }
  if (n > 0 && fread(buf, 1, (size_t)n, f) != (size_t)n) { perror("h_driver: fread"); return 2; }
  fclose(f);
  int r = LLVMFuzzerTestOneInput(buf, (size_t)n);
  printf("LLVMFuzzerTestOneInput returned %d\n", r);
  free(buf);
  return 0;
}
