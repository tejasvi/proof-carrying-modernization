/** Small arithmetic routines, verified in Examples/Basics.lean. */
public class Basics {
  /** The larger of two ints. */
  static int max(int a, int b) { return a < b ? b : a; }

  /** Clamp x into [lo, hi] (assumes lo <= hi). */
  static int clamp(int x, int lo, int hi) {
    if (x < lo) return lo;
    if (x > hi) return hi;
    return x;
  }

  /** 1 + 2 + ... + n, for 0 <= n <= 1000 (no overflow). */
  static int sumTo(int n) {
    int s = 0;
    for (int i = 1; i <= n; i++) s += i;
    return s;
  }

  /** Greatest common divisor by Euclid's algorithm, for a, b >= 0. */
  static int gcd(int a, int b) {
    while (b != 0) { int t = a % b; a = b; b = t; }
    return a;
  }

  /** Number of elements of an int array that are positive. */
  static int countPositive(int[] xs) {
    int c = 0;
    for (int i = 0; i < xs.length; i++) if (xs[i] > 0) c++;
    return c;
  }
}
