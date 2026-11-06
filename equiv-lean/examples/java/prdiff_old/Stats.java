/** Before the pull request: an index loop. */
public final class Stats {
    public static int total(int[] a) {
        int s = 0;
        for (int i = 0; i < a.length; i++) {
            s += a[i];
        }
        return s;
    }
}
