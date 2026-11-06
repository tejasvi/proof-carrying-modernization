/** Before the pull request: explicit comparisons. */
public final class Clamp {
    public static int clamp(int x, int lo, int hi) {
        if (x < lo) {
            return lo;
        }
        if (x > hi) {
            return hi;
        }
        return x;
    }
}
