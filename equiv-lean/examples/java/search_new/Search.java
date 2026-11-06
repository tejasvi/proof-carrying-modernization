/** After the change: an enhanced for loop with a flag and break. */
public final class Search {
    public static boolean contains(int[] a, int k) {
        boolean found = false;
        for (int x : a) {
            if (x == k) {
                found = true;
                break;
            }
        }
        return found;
    }
}
