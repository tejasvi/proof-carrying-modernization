// countBits, before: count the set bits of A.
int count_bits(unsigned A) {
  int count = 0;
  while (A != 0) {
    if (A & 1u) count = count + 1;
    A = A >> 1;
  }
  return count;
}
