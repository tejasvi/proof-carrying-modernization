/* C side of the C <-> Rust migration demo; the Rust side is examples/rust/bits/src/lib.rs. */
#include <stdint.h>

/* FNV-1a, 32 bits, over n bytes */
uint32_t fnv1a32(const uint8_t *data, unsigned long n) {
  uint32_t h = 0x811c9dc5u;
  for (unsigned long i = 0; i < n; i++) {
    h ^= data[i];
    h *= 0x01000193u;
  }
  return h;
}

/* number of set bits: clear the lowest set bit until zero */
uint32_t popcount(uint32_t x) {
  uint32_t v = x;
  uint32_t c = 0;
  while (v != 0) {
    v &= v - 1u;
    c += 1u;
  }
  return c;
}

/* reverse the 32 bits of a word */
uint32_t reverse_bits(uint32_t x) {
  uint32_t v = x;
  uint32_t r = 0;
  for (uint32_t i = 0; i < 32; i++) {
    r = (r << 1) | (v & 1u);
    v >>= 1;
  }
  return r;
}
