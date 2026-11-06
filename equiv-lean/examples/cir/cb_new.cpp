// countBits, after: the same loop with an extra guarded branch (never taken inside the loop).
int count_bits(unsigned A) {
  int count = 0;
  while (A != 0) {
    if (A == 0) break;
    if ((A & 1u) != 0) count++;
    A >>= 1;
  }
  return count;
}
