/** After the pull request: Math.max / Math.min. */
public final class Clamp {
    public static int clamp(int x, int lo, int hi) {
        return Math.max(lo, Math.min(x, hi));
    }
}
