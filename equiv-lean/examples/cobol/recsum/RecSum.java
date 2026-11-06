import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

/** Java rewrite of RECSUM.cob: running totals over the input records. */
public final class RecSum {
    public record In(byte[] id, BigDecimal amt) {}
    public record Out(byte[] id, BigDecimal total) {}

    public static List<Out> run(List<In> recs) {
        List<Out> out = new ArrayList<>();
        BigDecimal total = BigDecimal.valueOf(0, 2);
        for (In r : recs) {
            total = total.add(r.amt());
            out.add(new Out(r.id(), total));
        }
        return out;
    }
}
