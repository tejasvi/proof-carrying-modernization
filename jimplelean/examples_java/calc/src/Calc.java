public class Calc {
    static int total;

    static int sq(int x) {
        return x * x;
    }

    static int sumSq(int a, int b) {
        return sq(a) + sq(b);
    }

    static int add(int k) {
        total = total + k;
        return total;
    }

    public static void main(String[] args) {
        System.out.println(sumSq(3, 4) + " " + add(5));
    }
}
