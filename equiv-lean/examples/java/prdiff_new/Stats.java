/** After the pull request: an enhanced for loop. */
public final class Stats {
    public static int total(int[] a) {
        int s = 0;
        for (int x : a) {
            s += x;
        }
        return s;
    }
}
