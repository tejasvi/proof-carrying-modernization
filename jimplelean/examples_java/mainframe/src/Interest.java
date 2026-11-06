import java.math.BigDecimal;
import java.math.RoundingMode;

/** Java rewrites of COBOL statements; the COBOL and the proofs are in Examples/Mainframe.lean. */
public class Interest {

  /** COMPUTE INT ROUNDED = BAL * RATE / 1200 ON SIZE ERROR ...      (INT PIC S9(5)V99) */
  static BigDecimal monthlyInterest(BigDecimal bal, BigDecimal rate) {
    BigDecimal r = bal.multiply(rate).divide(BigDecimal.valueOf(1200), 2, RoundingMode.HALF_UP);
    if (r.abs().compareTo(BigDecimal.valueOf(100000)) >= 0) throw new ArithmeticException("SIZE ERROR");
    return r;
  }

  /** COMPUTE NET = GROSS * (100 - DISC) / 100   (NET PIC 9(5)V99: no ROUNDED, no ON SIZE ERROR,
      so the excess fraction digits are truncated and the high-order digits and the sign dropped) */
  static BigDecimal netAmount(BigDecimal gross, BigDecimal disc) {
    BigDecimal t = gross.multiply(BigDecimal.valueOf(100).subtract(disc))
        .divide(BigDecimal.valueOf(100), 2, RoundingMode.DOWN);
    return t.remainder(BigDecimal.valueOf(100000)).abs();
  }

  /** PERFORM VARYING I FROM 1 BY 1 UNTIL I > N
          ADD AMT(I) TO TOT ON SIZE ERROR ...                      (TOT PIC S9(7)V99) */
  static BigDecimal lineTotal(BigDecimal[] amt) {
    BigDecimal tot = BigDecimal.ZERO;
    for (int i = 0; i < amt.length; i++) {
      tot = tot.add(amt[i]).setScale(2, RoundingMode.DOWN);
      if (tot.abs().compareTo(BigDecimal.valueOf(10000000)) >= 0) throw new ArithmeticException("SIZE ERROR");
    }
    return tot;
  }

  public static void main(String[] args) {
    System.out.println(monthlyInterest(new BigDecimal("12345.67"), new BigDecimal("5.2500")));
    System.out.println(netAmount(new BigDecimal("123456.78"), new BigDecimal("12.5")));
    System.out.println(lineTotal(new BigDecimal[] { new BigDecimal("1.255"), new BigDecimal("-0.5") }));
  }
}
