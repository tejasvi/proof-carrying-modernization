import java.math.BigDecimal;
import java.math.RoundingMode;

/**
 * Java rewrite of ACCTINT.cob (one account record, simple daily interest), written from
 * coblean's examples/acctint/AcctInt.java with the same BigDecimal logic, but without a
 * record: the result is a final class with final fields.  The constants are computed in the
 * method, so the method does not depend on the class-initialization state of AcctInt.
 */
public final class AcctInt {
    public static final class Result {
        public final BigDecimal balance;
        public final BigDecimal interest;
        public final char status;

        public Result(BigDecimal balance, BigDecimal interest, char status) {
            this.balance = balance;
            this.interest = interest;
            this.status = status;
        }
    }

    /** @param balance {@code null} when the balance field holds LOW-VALUES */
    public static Result accrue(char type, BigDecimal balance, BigDecimal rate, int days) {
        BigDecimal zero2 = BigDecimal.valueOf(0, 2);
        BigDecimal bal = balance == null ? zero2 : balance;
        if (days == 0 || (type != 'S' && type != 'C')) {
            return new Result(bal, zero2, 'Z');
        }
        BigDecimal daily = rate.divide(BigDecimal.valueOf(365), 8, RoundingMode.HALF_UP);
        BigDecimal interest = bal.multiply(daily).multiply(BigDecimal.valueOf(days))
                                 .setScale(2, RoundingMode.HALF_UP);
        if (interest.abs().compareTo(BigDecimal.valueOf(1_000_000_000L)) >= 0) {
            return new Result(bal, zero2, 'E');
        }
        BigDecimal newBal = bal.add(interest);
        if (newBal.abs().compareTo(BigDecimal.valueOf(100_000_000_000L)) >= 0) {
            return new Result(bal, interest, 'E');
        }
        return new Result(newBal, interest, 'K');
    }
}
