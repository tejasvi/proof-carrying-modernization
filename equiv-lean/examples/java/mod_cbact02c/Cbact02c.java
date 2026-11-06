import java.util.ArrayList;
import java.util.List;

public final class Cbact02c {

    public static final class CardRecord {
        public String cardNum;
        public long cardAcctId;
        public long cardCvvCd;
        public String cardEmbossedName;
        public String cardExpiraionDate;
        public String cardActiveStatus;
        public String filler1;

        public CardRecord(String cardNum, long cardAcctId, long cardCvvCd, String cardEmbossedName,
                          String cardExpiraionDate, String cardActiveStatus, String filler1) {
            this.cardNum = cardNum;
            this.cardAcctId = cardAcctId;
            this.cardCvvCd = cardCvvCd;
            this.cardEmbossedName = cardEmbossedName;
            this.cardExpiraionDate = cardExpiraionDate;
            this.cardActiveStatus = cardActiveStatus;
            this.filler1 = filler1;
        }
    }

    public static final class Result {
        public List<String> displays = new ArrayList<String>();
        public boolean abended = false;
    }

    public static Result run(CardRecord[] cardfileFile) {
        Result r = new Result();
        r.displays.add("START OF EXECUTION OF PROGRAM CBACT02C");

        // 0000-CARDFILE-OPEN: OPEN always succeeds with status '00'
        String cardfileStatus = "00";
        long applResult = 8;
        if (cardfileStatus.equals("00")) {
            applResult = 0;
        } else {
            applResult = 12;
        }
        if (applResult != 0) {
            r.displays.add("ERROR OPENING CARDFILE");
            displayIoStatus(r, cardfileStatus);
            abend(r);
            return r;
        }

        // CARD-RECORD working storage, initialised (no VALUE clauses)
        CardRecord cardRecord = new CardRecord(spaces(16), 0L, 0L, spaces(50), spaces(10), spaces(1), spaces(59));
        String endOfFile = "N";
        int pos = 0;
        boolean atEof = false;
        int n = cardfileFile == null ? 0 : cardfileFile.length;

        while (!endOfFile.equals("Y")) {
            if (endOfFile.equals("N")) {
                // 1000-CARDFILE-GET-NEXT
                if (pos < n) {
                    CardRecord src = cardfileFile[pos];
                    pos++;
                    cardRecord = new CardRecord(src.cardNum, src.cardAcctId, src.cardCvvCd,
                            src.cardEmbossedName, src.cardExpiraionDate, src.cardActiveStatus, src.filler1);
                    cardfileStatus = "00";
                } else if (!atEof) {
                    atEof = true;
                    cardfileStatus = "10";
                } else {
                    cardfileStatus = "46";
                }
                if (cardfileStatus.equals("00")) {
                    applResult = 0;
                } else if (cardfileStatus.equals("10")) {
                    applResult = 16;
                } else {
                    applResult = 12;
                }
                if (applResult == 0) {
                    // continue
                } else if (applResult == 16) {
                    endOfFile = "Y";
                } else {
                    r.displays.add("ERROR READING CARDFILE");
                    displayIoStatus(r, cardfileStatus);
                    abend(r);
                    return r;
                }
                if (endOfFile.equals("N")) {
                    r.displays.add(formatCard(cardRecord));
                }
            }
        }

        // 9000-CARDFILE-CLOSE: CLOSE always succeeds with status '00'
        cardfileStatus = "00";
        applResult = 8;
        if (cardfileStatus.equals("00")) {
            applResult = applResult - applResult;
        } else {
            applResult = 12;
        }
        if (applResult != 0) {
            r.displays.add("ERROR CLOSING CARDFILE");
            displayIoStatus(r, cardfileStatus);
            abend(r);
            return r;
        }

        r.displays.add("END OF EXECUTION OF PROGRAM CBACT02C");
        return r;
    }

    private static void abend(Result r) {
        r.displays.add("ABENDING PROGRAM");
        r.abended = true;
    }

    private static void displayIoStatus(Result r, String status) {
        char s1 = status.charAt(0);
        char s2 = status.charAt(1);
        boolean numeric = s1 >= '0' && s1 <= '9' && s2 >= '0' && s2 <= '9';
        if (!numeric || s1 == '9') {
            int v = ((int) s2) & 0xFF;
            String d = zeroPad(v % 1000, 3);
            r.displays.add("FILE STATUS IS: NNNN" + s1 + d);
        } else {
            r.displays.add("FILE STATUS IS: NNNN" + "00" + s1 + s2);
        }
    }

    private static String formatCard(CardRecord c) {
        StringBuilder sb = new StringBuilder();
        sb.append(fix(c.cardNum, 16));
        sb.append(zeroPad(c.cardAcctId, 11));
        sb.append(zeroPad(c.cardCvvCd, 3));
        sb.append(fix(c.cardEmbossedName, 50));
        sb.append(fix(c.cardExpiraionDate, 10));
        sb.append(fix(c.cardActiveStatus, 1));
        sb.append(fix(c.filler1, 59));
        return sb.toString();
    }

    private static String fix(String s, int n) {
        StringBuilder sb = new StringBuilder();
        if (s == null) {
            s = "";
        }
        for (int i = 0; i < n; i++) {
            if (i < s.length()) {
                sb.append(s.charAt(i));
            } else {
                sb.append(' ');
            }
        }
        return sb.toString();
    }

    private static String spaces(int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            sb.append(' ');
        }
        return sb.toString();
    }

    private static String zeroPad(long v, int n) {
        if (v < 0) {
            v = -v;
        }
        char[] buf = new char[n];
        for (int i = n - 1; i >= 0; i--) {
            buf[i] = (char) ('0' + (int) (v % 10));
            v = v / 10;
        }
        return new String(buf);
    }
}