import java.math.BigDecimal;
import java.util.*;

interface Priced { BigDecimal price(); }

class Item implements Priced {
  final BigDecimal unit; final int qty;
  Item(BigDecimal u, int q) { unit = u; qty = q; }
  public BigDecimal price() { return unit.multiply(BigDecimal.valueOf(qty)); }
}

public class Hello {
  static int sum(int[] a) { int s = 0; for (int i = 0; i < a.length; i++) s += a[i]; return s; }
  static BigDecimal total(List<Priced> xs) {
    BigDecimal t = BigDecimal.ZERO;
    for (Priced p : xs) t = t.add(p.price());
    return t;
  }
  static int safeDiv(int a, int b) {
    try { return a / b; } catch (ArithmeticException e) { return -1; } finally { cnt++; }
  }
  static int cnt;
  public static void main(String[] args) {
    List<Priced> l = new ArrayList<>();
    l.add(new Item(new BigDecimal("1.25"), 3));
    System.out.println(total(l));
    System.out.println(safeDiv(7, 0) + " " + cnt);
    switch (args.length) { case 0: cnt = 5; break; case 7: cnt = 9; break; default: cnt = 1; }
  }
}
