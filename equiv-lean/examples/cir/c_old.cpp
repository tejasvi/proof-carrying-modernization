// Demo (c), version before the fix: `a + b` overflows for large inputs (undefined behaviour).
int average(int a, int b) {
  return (a + b) / 2;
}
