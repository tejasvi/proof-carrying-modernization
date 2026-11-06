import java.util.ArrayList;

/** (a) Map records to display lines. */
public final class MapLines {
    public static final class Rec {
        public final long id;
        public final String name;
        public Rec(long id, String name) { this.id = id; this.name = name; }
    }

    public static final class Result {
        public final ArrayList<String> displays;
        public final int rc;
        public Result(ArrayList<String> displays, int rc) { this.displays = displays; this.rc = rc; }
    }

    public static Result run(Rec[] recs) {
        ArrayList<String> out = new ArrayList<>();
        for (int i = 0; i < recs.length; i++) {
            Rec r = recs[i];
            out.add("REC " + r.id + " " + r.name);
        }
        return new Result(out, 0);
    }
}
