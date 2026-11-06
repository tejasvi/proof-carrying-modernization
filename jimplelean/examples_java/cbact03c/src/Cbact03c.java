import java.util.ArrayList;
import java.util.List;

public final class Cbact03c {

    public static final class CardXrefRecord {
        public String xrefCardNum;
        public long xrefCustId;
        public long xrefAcctId;
        public String filler1;

        public CardXrefRecord(String xrefCardNum, long xrefCustId, long xrefAcctId, String filler1) {
            this.xrefCardNum = xrefCardNum;
            this.xrefCustId = xrefCustId;
            this.xrefAcctId = xrefAcctId;
            this.filler1 = filler1;
        }
    }

    public static final class Result {
        public List<String> displays = new ArrayList<String>();
        public boolean abended;
    }

    private static final class State {
        Result result;
        CardXrefRecord[] file;
        int pos;
        boolean atEof;
        String xreffileStatus;
        long applResult;
        String endOfFile;
        String recCardNum;
        long recCustId;
        long recAcctId;
        String recFiller;
        boolean abended;
    }

    public static Result run(CardXrefRecord[] xreffileFile) {
        State s = new State();
        s.result = new Result();
        s.file = xreffileFile == null ? new CardXrefRecord[0] : xreffileFile;
        s.pos = 0;
        s.atEof = false;
        s.xreffileStatus = "  ";
        s.applResult = 0;
        s.endOfFile = "N";
        s.recCardNum = spaces(16);
        s.recCustId = 0;
        s.recAcctId = 0;
        s.recFiller = spaces(14);
        s.abended = false;

        s.result.displays.add("START OF EXECUTION OF PROGRAM CBACT03C");
        xreffileOpen(s);
        if (s.abended) {
            return finish(s);
        }

        while (!s.endOfFile.equals("Y")) {
            if (s.endOfFile.equals("N")) {
                getNext(s);
                if (s.abended) {
                    return finish(s);
                }
                if (s.endOfFile.equals("N")) {
                    s.result.displays.add(recordText(s));
                }
            }
        }

        xreffileClose(s);
        if (s.abended) {
            return finish(s);
        }

        s.result.displays.add("END OF EXECUTION OF PROGRAM CBACT03C");
        return finish(s);
    }

    private static Result finish(State s) {
        s.result.abended = s.abended;
        return s.result;
    }

    private static void getNext(State s) {
        // READ XREFFILE-FILE INTO CARD-XREF-RECORD
        if (s.atEof) {
            s.xreffileStatus = "46";
        } else if (s.pos >= s.file.length) {
            s.atEof = true;
            s.xreffileStatus = "10";
        } else {
            CardXrefRecord r = s.file[s.pos];
            s.pos++;
            s.recCardNum = fixLen(r.xrefCardNum, 16);
            s.recCustId = r.xrefCustId;
            s.recAcctId = r.xrefAcctId;
            s.recFiller = fixLen(r.filler1, 14);
            s.xreffileStatus = "00";
        }

        if (s.xreffileStatus.equals("00")) {
            s.applResult = 0;
            s.result.displays.add(recordText(s));
        } else {
            if (s.xreffileStatus.equals("10")) {
                s.applResult = 16;
            } else {
                s.applResult = 12;
            }
        }
        if (s.applResult == 0) {
            // CONTINUE
        } else {
            if (s.applResult == 16) {
                s.endOfFile = "Y";
            } else {
                s.result.displays.add("ERROR READING XREFFILE");
                displayIoStatus(s, s.xreffileStatus);
                abendProgram(s);
            }
        }
    }

    private static void xreffileOpen(State s) {
        s.applResult = 8;
        s.xreffileStatus = "00";
        if (s.xreffileStatus.equals("00")) {
            s.applResult = 0;
        } else {
            s.applResult = 12;
        }
        if (s.applResult != 0) {
            s.result.displays.add("ERROR OPENING XREFFILE");
            displayIoStatus(s, s.xreffileStatus);
            abendProgram(s);
        }
    }

    private static void xreffileClose(State s) {
        s.applResult = 8;
        s.xreffileStatus = "00";
        if (s.xreffileStatus.equals("00")) {
            s.applResult = s.applResult - s.applResult;
        } else {
            s.applResult = 12;
        }
        if (s.applResult != 0) {
            s.result.displays.add("ERROR CLOSING XREFFILE");
            displayIoStatus(s, s.xreffileStatus);
            abendProgram(s);
        }
    }

    private static void abendProgram(State s) {
        s.result.displays.add("ABENDING PROGRAM");
        s.abended = true;
    }

    private static void displayIoStatus(State s, String ioStatus) {
        char stat1 = ioStatus.charAt(0);
        char stat2 = ioStatus.charAt(1);
        boolean numeric = isDigit(stat1) && isDigit(stat2);
        if (!numeric || stat1 == '9') {
            long bin = ((long) stat2) & 0xFF;
            long v = bin % 1000;
            String ioStatus04 = String.valueOf(stat1) + zeroPad(v, 3);
            s.result.displays.add("FILE STATUS IS: NNNN" + ioStatus04);
        } else {
            String ioStatus04 = "00" + ioStatus;
            s.result.displays.add("FILE STATUS IS: NNNN" + ioStatus04);
        }
    }

    private static boolean isDigit(char c) {
        return c >= '0' && c <= '9';
    }

    private static String recordText(State s) {
        StringBuilder sb = new StringBuilder();
        sb.append(s.recCardNum);
        sb.append(zeroPad(s.recCustId, 9));
        sb.append(zeroPad(s.recAcctId, 11));
        sb.append(s.recFiller);
        return sb.toString();
    }

    private static String zeroPad(long value, int width) {
        long v = value < 0 ? -value : value;
        char[] out = new char[width];
        for (int i = width - 1; i >= 0; i--) {
            out[i] = (char) ('0' + (int) (v % 10));
            v = v / 10;
        }
        return new String(out);
    }

    private static String spaces(int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            sb.append(' ');
        }
        return sb.toString();
    }

    private static String fixLen(String str, int n) {
        String t = str == null ? "" : str;
        if (t.length() >= n) {
            return t.substring(0, n);
        }
        StringBuilder sb = new StringBuilder(t);
        while (sb.length() < n) {
            sb.append(' ');
        }
        return sb.toString();
    }
}