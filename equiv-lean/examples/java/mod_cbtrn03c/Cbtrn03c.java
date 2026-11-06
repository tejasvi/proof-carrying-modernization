import java.util.ArrayList;
import java.util.List;

public final class Cbtrn03c {

    // ------------------------------------------------------------------
    // Record classes
    // ------------------------------------------------------------------
    public static final class TranRecord {
        public String tranId;
        public String tranTypeCd;
        public long tranCatCd;
        public String tranSource;
        public String tranDesc;
        public long tranAmt;
        public long tranMerchantId;
        public String tranMerchantName;
        public String tranMerchantCity;
        public String tranMerchantZip;
        public String tranCardNum;
        public String tranOrigTs;
        public String tranProcTs;
        public String filler1;

        public TranRecord(String tranId, String tranTypeCd, long tranCatCd, String tranSource,
                          String tranDesc, long tranAmt, long tranMerchantId, String tranMerchantName,
                          String tranMerchantCity, String tranMerchantZip, String tranCardNum,
                          String tranOrigTs, String tranProcTs, String filler1) {
            this.tranId = tranId;
            this.tranTypeCd = tranTypeCd;
            this.tranCatCd = tranCatCd;
            this.tranSource = tranSource;
            this.tranDesc = tranDesc;
            this.tranAmt = tranAmt;
            this.tranMerchantId = tranMerchantId;
            this.tranMerchantName = tranMerchantName;
            this.tranMerchantCity = tranMerchantCity;
            this.tranMerchantZip = tranMerchantZip;
            this.tranCardNum = tranCardNum;
            this.tranOrigTs = tranOrigTs;
            this.tranProcTs = tranProcTs;
            this.filler1 = filler1;
        }
    }

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

    public static final class TranTypeRecord {
        public String tranType;
        public String tranTypeDesc;
        public String filler1;

        public TranTypeRecord(String tranType, String tranTypeDesc, String filler1) {
            this.tranType = tranType;
            this.tranTypeDesc = tranTypeDesc;
            this.filler1 = filler1;
        }
    }

    public static final class TranCatRecord {
        public String tranTypeCd;
        public long tranCatCd;
        public String tranCatTypeDesc;
        public String filler1;

        public TranCatRecord(String tranTypeCd, long tranCatCd, String tranCatTypeDesc, String filler1) {
            this.tranTypeCd = tranTypeCd;
            this.tranCatCd = tranCatCd;
            this.tranCatTypeDesc = tranCatTypeDesc;
            this.filler1 = filler1;
        }
    }

    public static final class WsDateparmRecord {
        public String wsStartDate;
        public String filler1;
        public String wsEndDate;

        public WsDateparmRecord(String wsStartDate, String filler1, String wsEndDate) {
            this.wsStartDate = wsStartDate;
            this.filler1 = filler1;
            this.wsEndDate = wsEndDate;
        }
    }

    public static final class FdReptfileRec {
        public String fdReptfileRec;

        public FdReptfileRec(String fdReptfileRec) {
            this.fdReptfileRec = fdReptfileRec;
        }
    }

    public static final class Result {
        public List<String> displays = new ArrayList<String>();
        public List<FdReptfileRec> reportFileWrites = new ArrayList<FdReptfileRec>();
        public boolean abended;
    }

    // ------------------------------------------------------------------
    // Working state
    // ------------------------------------------------------------------
    private static final class Ws {
        List<String> displays;
        List<FdReptfileRec> writes;
        boolean firstTime = true;
        String currCardNum = spaces(16);
        long xrefAcctId = 0;
        long lineCounter = 0;
        long pageTotal = 0;
        long accountTotal = 0;
        long grandTotal = 0;
        String startDate = spaces(10);
        String endDate = spaces(10);
    }

    private static final long MAX11 = 100000000000L;
    private static final long MAX9 = 1000000000L;

    // EBCDIC code page 037: character at index b is the Unicode character for EBCDIC byte b.
    private static final String CP037 =
        "\u0000\u0001\u0002\u0003\u009c\t\u0086\u007f\u0097\u008d\u008e\u000b\u000c\r\u000e\u000f"
      + "\u0010\u0011\u0012\u0013\u009d\u0085\b\u0087\u0018\u0019\u0092\u008f\u001c\u001d\u001e\u001f"
      + "\u0080\u0081\u0082\u0083\u0084\n\u0017\u001b\u0088\u0089\u008a\u008b\u008c\u0005\u0006\u0007"
      + "\u0090\u0091\u0016\u0093\u0094\u0095\u0096\u0004\u0098\u0099\u009a\u009b\u0014\u0015\u009e\u001a"
      + " \u00a0\u00e2\u00e4\u00e0\u00e1\u00e3\u00e5\u00e7\u00f1\u00a2.<(+|"
      + "&\u00e9\u00ea\u00eb\u00e8\u00ed\u00ee\u00ef\u00ec\u00df!$*);\u00ac"
      + "-/\u00c2\u00c4\u00c0\u00c1\u00c3\u00c5\u00c7\u00d1\u00a6,%_>?"
      + "\u00f8\u00c9\u00ca\u00cb\u00c8\u00cd\u00ce\u00cf\u00cc`:#@'=\""
      + "\u00d8abcdefghi\u00ab\u00bb\u00f0\u00fd\u00fe\u00b1"
      + "\u00b0jklmnopqr\u00aa\u00ba\u00e6\u00b8\u00c6\u00a4"
      + "\u00b5~stuvwxyz\u00a1\u00bf\u00d0\u00dd\u00de\u00ae"
      + "^\u00a3\u00a5\u00b7\u00a9\u00a7\u00b6\u00bc\u00bd\u00be[]\u00af\u00a8\u00b4\u00d7"
      + "{ABCDEFGHI\u00ad\u00f4\u00f6\u00f2\u00f3\u00f5"
      + "}JKLMNOPQR\u00b9\u00fb\u00fc\u00f9\u00fa\u00ff"
      + "\\\u00f7STUVWXYZ\u00b2\u00d4\u00d6\u00d2\u00d3\u00d5"
      + "0123456789\u00b3\u00db\u00dc\u00d9\u00da\u009f";

    // ------------------------------------------------------------------
    // Entry point
    // ------------------------------------------------------------------
    public static Result run(TranRecord[] transactFile, CardXrefRecord[] xrefFile,
                             TranTypeRecord[] trantypeFile, TranCatRecord[] trancatgFile,
                             WsDateparmRecord[] dateParmsFile) {
        Result r = new Result();
        Ws ws = new Ws();
        ws.displays = r.displays;
        ws.writes = r.reportFileWrites;

        r.displays.add("START OF EXECUTION OF PROGRAM CBTRN03C");

        boolean eof;
        if (dateParmsFile.length > 0) {
            ws.startDate = dateParmsFile[0].wsStartDate;
            ws.endDate = dateParmsFile[0].wsEndDate;
            r.displays.add("Reporting from " + ws.startDate + " to " + ws.endDate);
            eof = false;
        } else {
            eof = true;
        }

        TranRecord tran = blankTran();
        int pos = 0;
        while (!eof) {
            if (pos < transactFile.length) {
                tran = transactFile[pos];
                pos++;
            } else {
                eof = true;
            }
            String procDate = tran.tranProcTs.substring(0, 10);
            if (!(compareEbcdic(procDate, ws.startDate) >= 0
                    && compareEbcdic(procDate, ws.endDate) <= 0)) {
                // NEXT SENTENCE: leaves the inline PERFORM
                break;
            }
            if (!eof) {
                if (processDetail(ws, tran, xrefFile, trantypeFile, trancatgFile)) {
                    r.abended = true;
                    return r;
                }
            } else {
                processEnd(ws, tran);
            }
        }

        r.displays.add("END OF EXECUTION OF PROGRAM CBTRN03C");
        return r;
    }

    // ------------------------------------------------------------------
    // Per-record processing
    // ------------------------------------------------------------------
    private static boolean processDetail(Ws ws, TranRecord tran, CardXrefRecord[] xrefFile,
                                         TranTypeRecord[] trantypeFile, TranCatRecord[] trancatgFile) {
        ws.displays.add(tranRecordText(tran));
        if (!ws.currCardNum.equals(tran.tranCardNum)) {
            if (!ws.firstTime) {
                writeAccountTotals(ws);
            }
            ws.currCardNum = tran.tranCardNum;
            int xi = findXref(xrefFile, tran.tranCardNum);
            if (xi < 0) {
                ws.displays.add("INVALID CARD NUMBER : " + tran.tranCardNum);
                ws.displays.add(ioStatusLine("23"));
                ws.displays.add("ABENDING PROGRAM");
                return true;
            }
            ws.xrefAcctId = xrefFile[xi].xrefAcctId;
        }
        int ti = findTranType(trantypeFile, tran.tranTypeCd);
        if (ti < 0) {
            ws.displays.add("INVALID TRANSACTION TYPE : " + tran.tranTypeCd);
            ws.displays.add(ioStatusLine("23"));
            ws.displays.add("ABENDING PROGRAM");
            return true;
        }
        int ci = findTranCat(trancatgFile, tran.tranTypeCd, tran.tranCatCd);
        if (ci < 0) {
            ws.displays.add("INVALID TRAN CATG KEY : " + tran.tranTypeCd + digits(tran.tranCatCd, 4));
            ws.displays.add(ioStatusLine("23"));
            ws.displays.add("ABENDING PROGRAM");
            return true;
        }
        String typeDesc = trantypeFile[ti].tranTypeDesc;
        String catDesc = trancatgFile[ci].tranCatTypeDesc;
        writeTransactionReport(ws, tran, typeDesc, catDesc);
        return false;
    }

    private static void processEnd(Ws ws, TranRecord tran) {
        ws.displays.add("TRAN-AMT " + zoned(tran.tranAmt, 11));
        ws.displays.add("WS-PAGE-TOTAL" + zoned(ws.pageTotal, 11));
        ws.pageTotal = add11(ws.pageTotal, tran.tranAmt);
        ws.accountTotal = add11(ws.accountTotal, tran.tranAmt);
        writePageTotals(ws);
        writeGrandTotals(ws);
    }

    private static void writeTransactionReport(Ws ws, TranRecord tran, String typeDesc, String catDesc) {
        if (ws.firstTime) {
            ws.firstTime = false;
            writeHeaders(ws);
        }
        if (ws.lineCounter % 20 == 0) {
            writePageTotals(ws);
            writeHeaders(ws);
        }
        ws.pageTotal = add11(ws.pageTotal, tran.tranAmt);
        ws.accountTotal = add11(ws.accountTotal, tran.tranAmt);
        writeDetail(ws, tran, typeDesc, catDesc);
    }

    private static void writePageTotals(Ws ws) {
        StringBuilder sb = new StringBuilder();
        sb.append(pad("Page Total", 11));
        sb.append(repeat('.', 86));
        sb.append(edit(ws.pageTotal, true));
        writeLine(ws, sb.toString());
        ws.grandTotal = add11(ws.grandTotal, ws.pageTotal);
        ws.pageTotal = 0;
        incLine(ws);
        writeLine(ws, repeat('-', 133));
        incLine(ws);
    }

    private static void writeAccountTotals(Ws ws) {
        StringBuilder sb = new StringBuilder();
        sb.append(pad("Account Total", 13));
        sb.append(repeat('.', 84));
        sb.append(edit(ws.accountTotal, true));
        writeLine(ws, sb.toString());
        ws.accountTotal = 0;
        incLine(ws);
        writeLine(ws, repeat('-', 133));
        incLine(ws);
    }

    private static void writeGrandTotals(Ws ws) {
        StringBuilder sb = new StringBuilder();
        sb.append(pad("Grand Total", 11));
        sb.append(repeat('.', 86));
        sb.append(edit(ws.grandTotal, true));
        writeLine(ws, sb.toString());
    }

    private static void writeHeaders(Ws ws) {
        StringBuilder h = new StringBuilder();
        h.append(pad("DALYREPT", 38));
        h.append(pad("Daily Transaction Report", 41));
        h.append("Date Range: ");
        h.append(ws.startDate);
        h.append(" to ");
        h.append(ws.endDate);
        writeLine(ws, h.toString());
        incLine(ws);

        writeLine(ws, spaces(133));
        incLine(ws);

        StringBuilder h1 = new StringBuilder();
        h1.append(pad("Transaction ID", 17));
        h1.append(pad("Account ID", 12));
        h1.append(pad("Transaction Type", 19));
        h1.append(pad("Tran Category", 35));
        h1.append(pad("Tran Source", 14));
        h1.append(' ');
        h1.append(pad("        Amount", 16));
        writeLine(ws, h1.toString());
        incLine(ws);

        writeLine(ws, repeat('-', 133));
        incLine(ws);
    }

    private static void writeDetail(Ws ws, TranRecord tran, String typeDesc, String catDesc) {
        StringBuilder sb = new StringBuilder();
        sb.append(pad(tran.tranId, 16));
        sb.append(' ');
        sb.append(digits(ws.xrefAcctId, 11));
        sb.append(' ');
        sb.append(pad(tran.tranTypeCd, 2));
        sb.append('-');
        sb.append(pad(typeDesc, 15));
        sb.append(' ');
        sb.append(digits(tran.tranCatCd, 4));
        sb.append('-');
        sb.append(pad(catDesc, 29));
        sb.append(' ');
        sb.append(pad(tran.tranSource, 10));
        sb.append("    ");
        sb.append(edit(tran.tranAmt, false));
        sb.append("  ");
        writeLine(ws, sb.toString());
        incLine(ws);
    }

    private static void writeLine(Ws ws, String text) {
        ws.writes.add(new FdReptfileRec(pad(text, 133)));
    }

    private static void incLine(Ws ws) {
        ws.lineCounter = (ws.lineCounter + 1) % MAX9;
    }

    // ------------------------------------------------------------------
    // Keyed lookups
    // ------------------------------------------------------------------
    private static int findXref(CardXrefRecord[] f, String key) {
        for (int i = 0; i < f.length; i++) {
            if (f[i].xrefCardNum.equals(key)) {
                return i;
            }
        }
        return -1;
    }

    private static int findTranType(TranTypeRecord[] f, String key) {
        for (int i = 0; i < f.length; i++) {
            if (f[i].tranType.equals(key)) {
                return i;
            }
        }
        return -1;
    }

    private static int findTranCat(TranCatRecord[] f, String typeCd, long catCd) {
        for (int i = 0; i < f.length; i++) {
            if (f[i].tranTypeCd.equals(typeCd) && f[i].tranCatCd == catCd) {
                return i;
            }
        }
        return -1;
    }

    // ------------------------------------------------------------------
    // Formatting helpers
    // ------------------------------------------------------------------
    private static TranRecord blankTran() {
        return new TranRecord(spaces(16), spaces(2), 0, spaces(10), spaces(100), 0, 0,
                spaces(50), spaces(50), spaces(10), spaces(16), spaces(26), spaces(26), spaces(20));
    }

    private static String tranRecordText(TranRecord t) {
        StringBuilder sb = new StringBuilder();
        sb.append(t.tranId);
        sb.append(t.tranTypeCd);
        sb.append(digits(t.tranCatCd, 4));
        sb.append(t.tranSource);
        sb.append(t.tranDesc);
        sb.append(zoned(t.tranAmt, 11));
        sb.append(digits(t.tranMerchantId, 9));
        sb.append(t.tranMerchantName);
        sb.append(t.tranMerchantCity);
        sb.append(t.tranMerchantZip);
        sb.append(t.tranCardNum);
        sb.append(t.tranOrigTs);
        sb.append(t.tranProcTs);
        sb.append(t.filler1);
        return sb.toString();
    }

    private static String ioStatusLine(String st) {
        char s1 = st.charAt(0);
        char s2 = st.charAt(1);
        boolean numeric = s1 >= '0' && s1 <= '9' && s2 >= '0' && s2 <= '9';
        StringBuilder sb = new StringBuilder();
        sb.append("FILE STATUS IS: NNNN");
        if (!numeric || s1 == '9') {
            sb.append(s1);
            sb.append(digits(ebcdic(s2), 3));
        } else {
            sb.append("00");
            sb.append(st);
        }
        return sb.toString();
    }

    private static long add11(long a, long b) {
        return (a + b) % MAX11;
    }

    private static long pow10(int n) {
        long p = 1;
        for (int i = 0; i < n; i++) {
            p = p * 10;
        }
        return p;
    }

    private static String digits(long v, int n) {
        long m = v < 0 ? -v : v;
        m = m % pow10(n);
        StringBuilder sb = new StringBuilder();
        for (int i = n - 1; i >= 0; i--) {
            long p = pow10(i);
            sb.append((char) ('0' + (int) ((m / p) % 10)));
        }
        return sb.toString();
    }

    private static String zoned(long v, int n) {
        String d = digits(v, n);
        int last = d.charAt(n - 1) - '0';
        char o;
        if (v < 0) {
            o = last == 0 ? '}' : (char) ('J' + last - 1);
        } else {
            o = last == 0 ? '{' : (char) ('A' + last - 1);
        }
        StringBuilder sb = new StringBuilder();
        sb.append(d.substring(0, n - 1));
        sb.append(o);
        return sb.toString();
    }

    // PIC -ZZZ,ZZZ,ZZZ.ZZ (plusSign=false) or +ZZZ,ZZZ,ZZZ.ZZ (plusSign=true)
    private static String edit(long v, boolean plusSign) {
        long m = v < 0 ? -v : v;
        m = m % MAX11;
        if (m == 0) {
            return spaces(15);
        }
        String d = digits(m, 11);
        StringBuilder sb = new StringBuilder();
        if (v < 0) {
            sb.append('-');
        } else {
            sb.append(plusSign ? '+' : ' ');
        }
        boolean started = false;
        for (int i = 0; i < 9; i++) {
            if (i == 3 || i == 6) {
                sb.append(started ? ',' : ' ');
            }
            char c = d.charAt(i);
            if (!started && c == '0') {
                sb.append(' ');
            } else {
                started = true;
                sb.append(c);
            }
        }
        sb.append('.');
        sb.append(d.charAt(9));
        sb.append(d.charAt(10));
        return sb.toString();
    }

    private static String spaces(int n) {
        return repeat(' ', n);
    }

    private static String repeat(char c, int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            sb.append(c);
        }
        return sb.toString();
    }

    private static String pad(String s, int n) {
        if (s.length() >= n) {
            return s.substring(0, n);
        }
        StringBuilder sb = new StringBuilder();
        sb.append(s);
        for (int i = s.length(); i < n; i++) {
            sb.append(' ');
        }
        return sb.toString();
    }

    private static int compareEbcdic(String a, String b) {
        int n = a.length() < b.length() ? a.length() : b.length();
        for (int i = 0; i < n; i++) {
            int x = ebcdic(a.charAt(i));
            int y = ebcdic(b.charAt(i));
            if (x != y) {
                return x < y ? -1 : 1;
            }
        }
        if (a.length() > n) {
            for (int i = n; i < a.length(); i++) {
                int x = ebcdic(a.charAt(i));
                if (x != 0x40) {
                    return x < 0x40 ? -1 : 1;
                }
            }
        } else if (b.length() > n) {
            for (int i = n; i < b.length(); i++) {
                int y = ebcdic(b.charAt(i));
                if (y != 0x40) {
                    return 0x40 < y ? -1 : 1;
                }
            }
        }
        return 0;
    }

    // EBCDIC (code page 037) code of a character
    private static int ebcdic(char c) {
        for (int i = 0; i < 256; i++) {
            if (CP037.charAt(i) == c) {
                return i;
            }
        }
        return 0x6F;
    }
}