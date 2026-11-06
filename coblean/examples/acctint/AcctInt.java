import java.math.BigDecimal;
import java.math.RoundingMode;

/** Java rewrite of ACCTINT.cob (one account record, simple daily interest). */
public final class AcctInt {
    public record Result(BigDecimal balance, BigDecimal interest, char status) {}

    private static final BigDecimal ZERO2 = BigDecimal.valueOf(0, 2);
    private static final BigDecimal DAYS_PER_YEAR = BigDecimal.valueOf(365);
    private static final BigDecimal MAX_INTEREST = BigDecimal.valueOf(1_000_000_000L);   // S9(9)V99
    private static final BigDecimal MAX_BALANCE = BigDecimal.valueOf(100_000_000_000L);  // S9(11)V99

    /** @param balance {@code null} when the balance field holds LOW-VALUES */
    public static Result accrue(char type, BigDecimal balance, BigDecimal rate, int days) {
        BigDecimal bal = balance == null ? ZERO2 : balance;
        if (days == 0 || (type != 'S' && type != 'C')) {
            return new Result(bal, ZERO2, 'Z');
        }
        BigDecimal daily = rate.divide(DAYS_PER_YEAR, 8, RoundingMode.HALF_UP);
        BigDecimal interest = bal.multiply(daily).multiply(BigDecimal.valueOf(days))
                                 .setScale(2, RoundingMode.HALF_UP);
        if (interest.abs().compareTo(MAX_INTEREST) >= 0) {
            return new Result(bal, ZERO2, 'E');
        }
        BigDecimal newBal = bal.add(interest);
        if (newBal.abs().compareTo(MAX_BALANCE) >= 0) {
            return new Result(bal, interest, 'E');
        }
        return new Result(newBal, interest, 'K');
    }
}
