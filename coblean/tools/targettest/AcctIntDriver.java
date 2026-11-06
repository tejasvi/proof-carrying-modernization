import java.math.BigDecimal;
import java.io.BufferedReader;
import java.io.InputStreamReader;

/** Reads `type balance|null rate days` lines (balance at scale 2, rate at scale 5 as unscaled
 *  integers) and prints `balance interest status` (unscaled at scale 2) per line. */
public final class AcctIntDriver {
    public static void main(String[] args) throws Exception {
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        String line;
        while ((line = in.readLine()) != null) {
            String[] f = line.trim().split(" ");
            char type = f[0].charAt(0);
            BigDecimal bal = f[1].equals("null") ? null : BigDecimal.valueOf(Long.parseLong(f[1]), 2);
            BigDecimal rate = BigDecimal.valueOf(Long.parseLong(f[2]), 5);
            int days = Integer.parseInt(f[3]);
            AcctInt.Result r = AcctInt.accrue(type, bal, rate, days);
            System.out.println(r.balance().setScale(2).unscaledValue() + " "
                + r.interest().setScale(2).unscaledValue() + " " + r.status());
        }
    }
}
