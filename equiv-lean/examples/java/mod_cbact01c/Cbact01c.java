public final class Cbact01c {

    public static final class AccountRecord {
        public long acctId;
        public String acctActiveStatus;
        public long acctCurrBal;
        public long acctCreditLimit;
        public long acctCashCreditLimit;
        public String acctOpenDate;
        public String acctExpiraionDate;
        public String acctReissueDate;
        public long acctCurrCycCredit;
        public long acctCurrCycDebit;
        public String acctAddrZip;
        public String acctGroupId;
        public String filler1;

        public AccountRecord(long acctId, String acctActiveStatus, long acctCurrBal, long acctCreditLimit,
                             long acctCashCreditLimit, String acctOpenDate, String acctExpiraionDate,
                             String acctReissueDate, long acctCurrCycCredit, long acctCurrCycDebit,
                             String acctAddrZip, String acctGroupId, String filler1) {
            this.acctId = acctId;
            this.acctActiveStatus = acctActiveStatus;
            this.acctCurrBal = acctCurrBal;
            this.acctCreditLimit = acctCreditLimit;
            this.acctCashCreditLimit = acctCashCreditLimit;
            this.acctOpenDate = acctOpenDate;
            this.acctExpiraionDate = acctExpiraionDate;
            this.acctReissueDate = acctReissueDate;
            this.acctCurrCycCredit = acctCurrCycCredit;
            this.acctCurrCycDebit = acctCurrCycDebit;
            this.acctAddrZip = acctAddrZip;
            this.acctGroupId = acctGroupId;
            this.filler1 = filler1;
        }
    }

    public static final class OutAcctRec {
        public long outAcctId;
        public String outAcctActiveStatus;
        public long outAcctCurrBal;
        public long outAcctCreditLimit;
        public long outAcctCashCreditLimit;
        public String outAcctOpenDate;
        public String outAcctExpiraionDate;
        public String outAcctReissueDate;
        public long outAcctCurrCycCredit;
        public long outAcctCurrCycDebit;
        public String outAcctGroupId;

        public OutAcctRec(long outAcctId, String outAcctActiveStatus, long outAcctCurrBal,
                          long outAcctCreditLimit, long outAcctCashCreditLimit, String outAcctOpenDate,
                          String outAcctExpiraionDate, String outAcctReissueDate, long outAcctCurrCycCredit,
                          long outAcctCurrCycDebit, String outAcctGroupId) {
            this.outAcctId = outAcctId;
            this.outAcctActiveStatus = outAcctActiveStatus;
            this.outAcctCurrBal = outAcctCurrBal;
            this.outAcctCreditLimit = outAcctCreditLimit;
            this.outAcctCashCreditLimit = outAcctCashCreditLimit;
            this.outAcctOpenDate = outAcctOpenDate;
            this.outAcctExpiraionDate = outAcctExpiraionDate;
            this.outAcctReissueDate = outAcctReissueDate;
            this.outAcctCurrCycCredit = outAcctCurrCycCredit;
            this.outAcctCurrCycDebit = outAcctCurrCycDebit;
            this.outAcctGroupId = outAcctGroupId;
        }
    }

    public static final class ArrArrayRec {
        public long arrAcctId;
        public long[] arrAcctCurrBal;
        public long[] arrAcctCurrCycDebit;
        public String arrFiller;

        public ArrArrayRec(long arrAcctId, long[] arrAcctCurrBal, long[] arrAcctCurrCycDebit, String arrFiller) {
            this.arrAcctId = arrAcctId;
            this.arrAcctCurrBal = arrAcctCurrBal;
            this.arrAcctCurrCycDebit = arrAcctCurrCycDebit;
            this.arrFiller = arrFiller;
        }
    }

    public static final class Result {
        public java.util.List<String> displays = new java.util.ArrayList<String>();
        public java.util.List<OutAcctRec> outFileWrites = new java.util.ArrayList<OutAcctRec>();
        public java.util.List<ArrArrayRec> arryFileWrites = new java.util.ArrayList<ArrArrayRec>();
        public java.util.List<String> vbrcFileWrites = new java.util.ArrayList<String>();
        public boolean abended;
    }

    public static Result run(AccountRecord[] acctfileFile) {
        Result r = new Result();
        r.displays.add("START OF EXECUTION OF PROGRAM CBACT01C");
        // OPENs always succeed (status '00')

        long outCycDebit = 0;                 // OUT-ACCT-CURR-CYC-DEBIT persists in the FD area
        String codatecnOutDate = spaces(20);  // CODATECN-0UT-DATE persists in WORKING-STORAGE
        int pos = 0;
        boolean pastEnd = false;
        boolean endOfFile = false;

        while (!endOfFile) {
            String status;
            AccountRecord rec = null;
            if (pos < acctfileFile.length) {
                status = "00";
                rec = acctfileFile[pos];
                pos++;
            } else if (!pastEnd) {
                status = "10";
                pastEnd = true;
            } else {
                status = "46";
            }

            if (status.equals("00")) {
                displayAcctRecord(r, rec);
                codatecnOutDate = cobdatft("2", pad(rec.acctReissueDate, 20), "2", codatecnOutDate);
                if (rec.acctCurrCycDebit == 0) {
                    outCycDebit = 252500L;
                }
                writeOutRecord(r, rec, codatecnOutDate, outCycDebit);
                writeArrayRecord(r, rec);
                writeVbrcRecords(r, rec);
                r.displays.add(accountRecordText(rec));
            } else if (status.equals("10")) {
                endOfFile = true;
            } else {
                r.displays.add("ERROR READING ACCOUNT FILE");
                displayIoStatus(r, status);
                r.displays.add("ABENDING PROGRAM");
                r.abended = true;
                return r;
            }
        }

        // CLOSE always succeeds (status '00')
        r.displays.add("END OF EXECUTION OF PROGRAM CBACT01C");
        return r;
    }

    private static void displayAcctRecord(Result r, AccountRecord a) {
        r.displays.add("ACCT-ID                 :" + zoned(a.acctId, 11, false));
        r.displays.add("ACCT-ACTIVE-STATUS      :" + a.acctActiveStatus);
        r.displays.add("ACCT-CURR-BAL           :" + zoned(a.acctCurrBal, 12, true));
        r.displays.add("ACCT-CREDIT-LIMIT       :" + zoned(a.acctCreditLimit, 12, true));
        r.displays.add("ACCT-CASH-CREDIT-LIMIT  :" + zoned(a.acctCashCreditLimit, 12, true));
        r.displays.add("ACCT-OPEN-DATE          :" + a.acctOpenDate);
        r.displays.add("ACCT-EXPIRAION-DATE     :" + a.acctExpiraionDate);
        r.displays.add("ACCT-REISSUE-DATE       :" + a.acctReissueDate);
        r.displays.add("ACCT-CURR-CYC-CREDIT    :" + zoned(a.acctCurrCycCredit, 12, true));
        r.displays.add("ACCT-CURR-CYC-DEBIT     :" + zoned(a.acctCurrCycDebit, 12, true));
        r.displays.add("ACCT-GROUP-ID           :" + a.acctGroupId);
        r.displays.add("-------------------------------------------------");
    }

    private static void writeOutRecord(Result r, AccountRecord a, String codatecnOutDate, long outCycDebit) {
        OutAcctRec o = new OutAcctRec(
                a.acctId,
                pad(a.acctActiveStatus, 1),
                a.acctCurrBal,
                a.acctCreditLimit,
                a.acctCashCreditLimit,
                pad(a.acctOpenDate, 10),
                pad(a.acctExpiraionDate, 10),
                pad(codatecnOutDate, 10),
                a.acctCurrCycCredit,
                outCycDebit,
                pad(a.acctGroupId, 10));
        // WRITE to sequential file: status '00'
        r.outFileWrites.add(o);
    }

    private static void writeArrayRecord(Result r, AccountRecord a) {
        long[] bal = new long[5];
        long[] deb = new long[5];
        bal[0] = a.acctCurrBal;
        deb[0] = 100500L;
        bal[1] = a.acctCurrBal;
        deb[1] = 152500L;
        bal[2] = -102500L;
        deb[2] = -250000L;
        ArrArrayRec ar = new ArrArrayRec(a.acctId, bal, deb, spaces(4));
        // WRITE to sequential file: status '00'
        r.arryFileWrites.add(ar);
    }

    private static void writeVbrcRecords(Result r, AccountRecord a) {
        StringBuilder rec1 = new StringBuilder();
        rec1.append(zoned(a.acctId, 11, false));
        rec1.append(pad(a.acctActiveStatus, 1));
        StringBuilder rec2 = new StringBuilder();
        rec2.append(zoned(a.acctId, 11, false));
        rec2.append(zoned(a.acctCurrBal, 12, true));
        rec2.append(zoned(a.acctCreditLimit, 12, true));
        rec2.append(pad(a.acctReissueDate, 10).substring(0, 4));
        String s1 = rec1.toString();
        String s2 = rec2.toString();
        r.displays.add("VBRC-REC1:" + s1);
        r.displays.add("VBRC-REC2:" + s2);
        // WRITE length 12, then length 39: status '00'
        r.vbrcFileWrites.add(s1);
        r.vbrcFileWrites.add(s2);
    }

    private static String accountRecordText(AccountRecord a) {
        StringBuilder sb = new StringBuilder();
        sb.append(zoned(a.acctId, 11, false));
        sb.append(pad(a.acctActiveStatus, 1));
        sb.append(zoned(a.acctCurrBal, 12, true));
        sb.append(zoned(a.acctCreditLimit, 12, true));
        sb.append(zoned(a.acctCashCreditLimit, 12, true));
        sb.append(pad(a.acctOpenDate, 10));
        sb.append(pad(a.acctExpiraionDate, 10));
        sb.append(pad(a.acctReissueDate, 10));
        sb.append(zoned(a.acctCurrCycCredit, 12, true));
        sb.append(zoned(a.acctCurrCycDebit, 12, true));
        sb.append(pad(a.acctAddrZip, 10));
        sb.append(pad(a.acctGroupId, 10));
        sb.append(pad(a.filler1, 178));
        return sb.toString();
    }

    // COBDATFT assembler routine: returns the new CODATECN-0UT-DATE (20 chars).
    private static String cobdatft(String inType, String inpDate, String outType, String outDate) {
        if (inType.equals("1")) {
            if (inpDate.charAt(4) == '-') {
                return outDate; // GOTOERR (error message not used by caller)
            }
            if (outType.equals("2")) {
                return outDate;
            }
            StringBuilder sb = new StringBuilder();
            sb.append(inpDate.substring(0, 4));
            sb.append('-');
            sb.append(inpDate.substring(4, 6));
            sb.append('-');
            sb.append(inpDate.substring(6, 8));
            sb.append(outDate.substring(10));
            return sb.toString();
        } else if (inType.equals("2")) {
            if (outType.equals("1")) {
                return outDate;
            }
            StringBuilder sb = new StringBuilder();
            sb.append(inpDate.substring(0, 4));
            sb.append(inpDate.substring(5, 7));
            sb.append(inpDate.substring(8, 10));
            sb.append(outDate.substring(8));
            return sb.toString();
        }
        return outDate;
    }

    private static void displayIoStatus(Result r, String io) {
        char s1 = io.charAt(0);
        char s2 = io.charAt(1);
        boolean numeric = s1 >= '0' && s1 <= '9' && s2 >= '0' && s2 <= '9';
        if (!numeric || s1 == '9') {
            int code = ebcdic(s2) % 1000;
            StringBuilder sb = new StringBuilder();
            sb.append("FILE STATUS IS: NNNN");
            sb.append(s1);
            sb.append((char) ('0' + (code / 100) % 10));
            sb.append((char) ('0' + (code / 10) % 10));
            sb.append((char) ('0' + code % 10));
            r.displays.add(sb.toString());
        } else {
            r.displays.add("FILE STATUS IS: NNNN00" + io);
        }
    }

    private static int ebcdic(char c) {
        if (c >= '0' && c <= '9') return 240 + (c - '0');
        if (c >= 'A' && c <= 'I') return 193 + (c - 'A');
        if (c >= 'J' && c <= 'R') return 209 + (c - 'J');
        if (c >= 'S' && c <= 'Z') return 226 + (c - 'S');
        if (c == ' ') return 64;
        return 0;
    }

    private static String zoned(long v, int digits, boolean signed) {
        boolean neg = v < 0;
        long a = neg ? -v : v;
        long div = 1;
        for (int i = 1; i < digits; i++) {
            div = div * 10;
        }
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < digits; i++) {
            int d = (int) ((a / div) % 10);
            if (i == digits - 1 && signed) {
                if (neg) {
                    sb.append(d == 0 ? '}' : (char) ('J' + d - 1));
                } else {
                    sb.append(d == 0 ? '{' : (char) ('A' + d - 1));
                }
            } else {
                sb.append((char) ('0' + d));
            }
            div = div / 10;
        }
        return sb.toString();
    }

    private static String pad(String s, int n) {
        StringBuilder sb = new StringBuilder();
        int len = s == null ? 0 : s.length();
        for (int i = 0; i < n; i++) {
            if (i < len) {
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
}