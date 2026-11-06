import java.util.*;
import java.util.function.*;

interface Shape { double area(); default String kind() { return "shape"; } }
enum Color { RED, GREEN }
abstract class Base { abstract int f(int x); int g() { return f(1) + 1; } }
class Derived extends Base { int f(int x) { return x * 2; } }

public class Probe {
  static final long BIG = 123456789012L;
  static float ff = 1.5f;
  static double dd = 2.25e10;
  static char c = 'x';
  static String s = "a\"b\\c\n\té";
  static int[][] grid = new int[3][4];
  static Object lock = new Object();
  int from; // keyword-like field
  static int ops(int a, int b, long l, float f, double d, byte by, short sh, char ch) {
    int r = a + b - a * b / (b == 0 ? 1 : b) % 7;
    r = r << 3 | r >> 2 ^ r >>> 1 & 0xFF;
    long q = l * 3 + (long) a; if (q > l) r++;
    if (f < 1.0f) r--; if (d >= 2.0) r += 2; if (Double.isNaN(d)) r = 0;
    r += (int) f + (int) d + by + sh + ch + (byte) a + (short) a + (char) a;
    long neg = -l; double nd = -d; float nf = -f;
    return r + (int) neg + (int) nd + (int) nf + (int) (q >>> 2) + (int)(l % 3L);
  }
  static int sw(int k, String s) {
    int r;
    switch (k) { case 1: r = 10; break; case 2: r = 20; break; case 3: r = 30; break; default: r = 0; }
    switch (s) { case "aa": r += 1; break; case "bb": r += 2; break; default: r += 3; }
    return r;
  }
  static Object misc(Object o) {
    synchronized (lock) { if (o instanceof String) return ((String) o).length(); }
    Class<?> k = String.class;
    int[] a = new int[5]; a[2] = 7;
    String[] sa = new String[2];
    Object[][] m = new Object[2][];
    return a.length + sa.length + m.length;
  }
  static String concat11(String a, int b) { return a + b + "!"; }
  static int lam(List<Integer> xs) { Function<Integer,Integer> f = x -> x + 1; int s = 0; for (int x : xs) s += f.apply(x); return s; }
  static int col(Color col) { switch (col) { case RED: return 1; default: return 2; } }
  public static void main(String[] args) throws Exception {
    System.out.println(ops(1,2,3L,4f,5.0,(byte)6,(short)7,'8'));
    if (args.length > 100) throw new IllegalStateException("x");
  }
}
