/** Before the change: an index loop that returns as soon as it finds the key. */
public final class Search {
    public static boolean contains(int[] a, int k) {
        for (int i = 0; i < a.length; i++) {
            if (a[i] == k) {
                return true;
            }
        }
        return false;
    }
}
