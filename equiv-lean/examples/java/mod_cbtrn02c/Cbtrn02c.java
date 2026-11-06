import java.util.ArrayList;
import java.util.List;

public final class Cbtrn02c {

    // ------------------------------------------------------------------
    // Record classes
    // ------------------------------------------------------------------

    public static final class DalytranRecord {
        public String dalytranId;
        public String dalytranTypeCd;
        public long dalytranCatCd;
        public String dalytranSource;
        public String dalytranDesc;
        public long dalytranAmt;
        public long dalytranMerchantId;
        public String dalytranMerchantName;
        public String dalytranMerchantCity;
        public String dalytranMerchantZip;
        public String dalytranCardNum;
        public String dalytranOrigTs;
        public String dalytranProcTs;
        public String filler1;

        public DalytranRecord(String dalytranId, String dalytranTypeCd, long dalytranCatCd,
                              String dalytranSource, String dalytranDesc, long dalytranAmt,
                              long dalytranMerchantId, String dalytranMerchantName,
                              String dalytranMerchantCity, String dalytranMerchantZip,
                              String dalytranCardNum, String dalytranOrigTs,
                              String dalytranProcTs, String filler1) {
            this.dalytranId = dalytranId;
            this.dalytranTypeCd = dalytranTypeCd;
            this.dalytranCatCd = dalytranCatCd;
            this.dalytranSource = dalytranSource;
            this.dalytranDesc = dalytranDesc;
            this.dalytranAmt = dalytranAmt;
            this.dalytranMerchantId = dalytranMerchantId;
            this.dalytranMerchantName = dalytranMerchantName;
            this.dalytranMerchantCity = dalytranMerchantCity;
            this.dalytranMerchantZip = dalytranMerchantZip;
            this.dalytranCardNum = dalytranCardNum;
            this.dalytranOrigTs = dalytranOrigTs;
            this.dalytranProcTs = dalytranProcTs;
            this.filler1 = filler1;
        }
    }

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
                          String tranDesc, long tranAmt, long tranMerchantId,
                          String tranMerchantName, String tranMerchantCity,
                          String tranMerchantZip, String tranCardNum, String tranOrigTs,
                          String tranProcTs, String filler1) {
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

        public AccountRecord(long acctId, String acctActiveStatus, long acctCurrBal,
                             long acctCreditLimit, long acctCashCreditLimit, String acctOpenDate,
                             String acctExpiraionDate, String acctReissueDate,
                             long acctCurrCycCredit, long acctCurrCycDebit, String acctAddrZip,
                             String acctGroupId, String filler1) {
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

    public static final class TranCatBalRecord {
        public long trancatAcctId;
        public String trancatTypeCd;
        public long trancatCd;
        public long tranCatBal;
        public String filler1;

        public TranCatBalRecord(long trancatAcctId, String trancatTypeCd, long trancatCd,
                                long tranCatBal, String filler1) {
            this.trancatAcctId = trancatAcctId;
            this.trancatTypeCd = trancatTypeCd;
            this.trancatCd = trancatCd;
            this.tranCatBal = tranCatBal;
            this.filler1 = filler1;
        }
    }

    public static final class RejectRecord {
        public String rejectTranData;
        public String validationTrailer;

        public RejectRecord(String rejectTranData, String validationTrailer) {
            this.rejectTranData = rejectTranData;
            this.validationTrailer = validationTrailer;
        }
    }

    public static final class Result {
        public List<String> displays = new ArrayList<String>();
        public List<TranRecord> transactFileWrites = new ArrayList<TranRecord>();
        public List<RejectRecord> dalyrejsFileWrites = new ArrayList<RejectRecord>();
        public List<TranCatBalRecord> tcatbalFileWrites = new ArrayList<TranCatBalRecord>();
        public List<AccountRecord> accountFileRewrites = new ArrayList<AccountRecord>();
        public List<TranCatBalRecord> tcatbalFileRewrites = new ArrayList<TranCatBalRecord>();
        public int returnCode;
        public boolean abended;
    }

    private static final long MOD9 = 1000000000L;
    private static final long MOD11 = 100000000000L;
    private static final long MOD12 = 1000000000000L;

    // ------------------------------------------------------------------
    // Entry point
    // ------------------------------------------------------------------

    public static Result run(DalytranRecord[] dalytranFile, CardXrefRecord[] xrefFile,
                             AccountRecord[] accountFile, TranCatBalRecord[] tcatbalFile,
                             String clock) {
        Result r = new Result();
        r.displays.add("START OF EXECUTION OF PROGRAM CBTRN02C");

        AccountRecord[] acctData = new AccountRecord[accountFile.length];
        for (int i = 0; i < accountFile.length; i++) {
            acctData[i] = copyAccount(accountFile[i]);
        }
        List<TranCatBalRecord> tcatData = new ArrayList<TranCatBalRecord>();
        for (int i = 0; i < tcatbalFile.length; i++) {
            tcatData.add(copyTcat(tcatbalFile[i]));
        }
        List<String> tranKeys = new ArrayList<String>();

        CardXrefRecord xrefWs = new CardXrefRecord(spaces(16), 0L, 0L, spaces(14));
        AccountRecord acctWs = new AccountRecord(0L, spaces(1), 0L, 0L, 0L, spaces(10),
                spaces(10), spaces(10), 0L, 0L, spaces(10), spaces(10), spaces(178));
        TranCatBalRecord tcatWs = new TranCatBalRecord(0L, spaces(2), 0L, 0L, spaces(22));
        TranRecord tranWs = new TranRecord(spaces(16), spaces(2), 0L, spaces(10), spaces(100),
                0L, 0L, spaces(50), spaces(50), spaces(10), spaces(16), spaces(26),
                spaces(26), spaces(20));

        long txCount = 0;
        long rejCount = 0;
        int next = 0;
        boolean eof = false;
        while (!eof) {
            if (next >= dalytranFile.length) {
                eof = true;
            } else {
                DalytranRecord d = dalytranFile[next];
                next++;
                txCount = (txCount + 1) % MOD9;
                int reason = validateTran(d, xrefFile, acctData, xrefWs, acctWs);
                if (reason == 0) {
                    boolean ab = postTransaction(r, d, clock, xrefWs, acctWs, tcatWs, tranWs,
                            acctData, tcatData, tranKeys);
                    if (ab) {
                        return r;
                    }
                } else {
                    rejCount = (rejCount + 1) % MOD9;
                    writeReject(r, d, reason);
                }
            }
        }

        r.displays.add("TRANSACTIONS PROCESSED :" + padNum(txCount, 9));
        r.displays.add("TRANSACTIONS REJECTED  :" + padNum(rejCount, 9));
        if (rejCount > 0) {
            r.returnCode = 4;
        }
        r.displays.add("END OF EXECUTION OF PROGRAM CBTRN02C");
        return r;
    }

    // ------------------------------------------------------------------
    // Validation
    // ------------------------------------------------------------------

    private static int validateTran(DalytranRecord d, CardXrefRecord[] xrefFile,
                                    AccountRecord[] acctData, CardXrefRecord xrefWs,
                                    AccountRecord acctWs) {
        int ix = findXref(xrefFile, d.dalytranCardNum);
        if (ix < 0) {
            return 100;
        }
        assignXref(xrefWs, xrefFile[ix]);
        int ia = findAccount(acctData, xrefWs.xrefAcctId);
        if (ia < 0) {
            return 101;
        }
        assignAccount(acctWs, acctData[ia]);
        int reason = 0;
        long temp = (acctWs.acctCurrCycCredit - acctWs.acctCurrCycDebit + d.dalytranAmt) % MOD11;
        if (!(acctWs.acctCreditLimit >= temp)) {
            reason = 102;
        }
        if (compareEbcdic(acctWs.acctExpiraionDate, d.dalytranOrigTs.substring(0, 10)) < 0) {
            reason = 103;
        }
        return reason;
    }

    private static String reasonDesc(int reason) {
        switch (reason) {
            case 100:
                return "INVALID CARD NUMBER FOUND";
            case 101:
                return "ACCOUNT RECORD NOT FOUND";
            case 102:
                return "OVERLIMIT TRANSACTION";
            case 103:
                return "TRANSACTION RECEIVED AFTER ACCT EXPIRATION";
            default:
                return "";
        }
    }

    // ------------------------------------------------------------------
    // Posting
    // ------------------------------------------------------------------

    private static boolean postTransaction(Result r, DalytranRecord d, String clock,
                                           CardXrefRecord xrefWs, AccountRecord acctWs,
                                           TranCatBalRecord tcatWs, TranRecord tranWs,
                                           AccountRecord[] acctData,
                                           List<TranCatBalRecord> tcatData,
                                           List<String> tranKeys) {
        tranWs.tranId = d.dalytranId;
        tranWs.tranTypeCd = d.dalytranTypeCd;
        tranWs.tranCatCd = d.dalytranCatCd;
        tranWs.tranSource = d.dalytranSource;
        tranWs.tranDesc = d.dalytranDesc;
        tranWs.tranAmt = d.dalytranAmt;
        tranWs.tranMerchantId = d.dalytranMerchantId;
        tranWs.tranMerchantName = d.dalytranMerchantName;
        tranWs.tranMerchantCity = d.dalytranMerchantCity;
        tranWs.tranMerchantZip = d.dalytranMerchantZip;
        tranWs.tranCardNum = d.dalytranCardNum;
        tranWs.tranOrigTs = d.dalytranOrigTs;
        tranWs.tranProcTs = db2Timestamp(clock);

        if (updateTcatbal(r, d, xrefWs, tcatWs, tcatData)) {
            return true;
        }
        updateAccount(r, d, acctWs, acctData);
        return writeTransaction(r, tranWs, tranKeys);
    }

    private static boolean updateTcatbal(Result r, DalytranRecord d, CardXrefRecord xrefWs,
                                         TranCatBalRecord tcatWs,
                                         List<TranCatBalRecord> tcatData) {
        long keyAcct = xrefWs.xrefAcctId;
        String keyType = d.dalytranTypeCd;
        long keyCd = d.dalytranCatCd;
        boolean create = false;
        int it = findTcatbal(tcatData, keyAcct, keyType, keyCd);
        if (it < 0) {
            r.displays.add("TCATBAL record not found for key : " + padNum(keyAcct, 11)
                    + keyType + padNum(keyCd, 4) + ".. Creating.");
            create = true;
        } else {
            assignTcat(tcatWs, tcatData.get(it));
        }
        if (create) {
            // INITIALIZE leaves FILLER unchanged
            tcatWs.trancatAcctId = 0;
            tcatWs.trancatTypeCd = spaces(2);
            tcatWs.trancatCd = 0;
            tcatWs.tranCatBal = 0;
            tcatWs.trancatAcctId = xrefWs.xrefAcctId;
            tcatWs.trancatTypeCd = d.dalytranTypeCd;
            tcatWs.trancatCd = d.dalytranCatCd;
            tcatWs.tranCatBal = (tcatWs.tranCatBal + d.dalytranAmt) % MOD11;
            int dup = findTcatbal(tcatData, tcatWs.trancatAcctId, tcatWs.trancatTypeCd,
                    tcatWs.trancatCd);
            if (dup >= 0) {
                abend(r, "ERROR WRITING TRANSACTION BALANCE FILE", "22");
                return true;
            }
            tcatData.add(copyTcat(tcatWs));
            r.tcatbalFileWrites.add(copyTcat(tcatWs));
        } else {
            tcatWs.tranCatBal = (tcatWs.tranCatBal + d.dalytranAmt) % MOD11;
            int ir = findTcatbal(tcatData, tcatWs.trancatAcctId, tcatWs.trancatTypeCd,
                    tcatWs.trancatCd);
            if (ir < 0) {
                abend(r, "ERROR REWRITING TRANSACTION BALANCE FILE", "23");
                return true;
            }
            tcatData.set(ir, copyTcat(tcatWs));
            r.tcatbalFileRewrites.add(copyTcat(tcatWs));
        }
        return false;
    }

    private static void updateAccount(Result r, DalytranRecord d, AccountRecord acctWs,
                                      AccountRecord[] acctData) {
        acctWs.acctCurrBal = (acctWs.acctCurrBal + d.dalytranAmt) % MOD12;
        if (d.dalytranAmt >= 0) {
            acctWs.acctCurrCycCredit = (acctWs.acctCurrCycCredit + d.dalytranAmt) % MOD12;
        } else {
            acctWs.acctCurrCycDebit = (acctWs.acctCurrCycDebit + d.dalytranAmt) % MOD12;
        }
        int ia = findAccount(acctData, acctWs.acctId);
        if (ia >= 0) {
            acctData[ia] = copyAccount(acctWs);
            r.accountFileRewrites.add(copyAccount(acctWs));
        }
        // INVALID KEY only sets reason 109, which has no further effect.
    }

    private static boolean writeTransaction(Result r, TranRecord tranWs, List<String> tranKeys) {
        int dup = findKey(tranKeys, tranWs.tranId);
        if (dup >= 0) {
            abend(r, "ERROR WRITING TO TRANSACTION FILE", "22");
            return true;
        }
        tranKeys.add(tranWs.tranId);
        r.transactFileWrites.add(copyTran(tranWs));
        return false;
    }

    private static void writeReject(Result r, DalytranRecord d, int reason) {
        String data = dalytranText(d);
        String trailer = padNum(reason, 4) + fit(reasonDesc(reason), 76);
        r.dalyrejsFileWrites.add(new RejectRecord(data, trailer));
    }

    // ------------------------------------------------------------------
    // Abend / IO status
    // ------------------------------------------------------------------

    private static void abend(Result r, String message, String status) {
        r.displays.add(message);
        displayIoStatus(r, status);
        r.displays.add("ABENDING PROGRAM");
        r.abended = true;
    }

    private static void displayIoStatus(Result r, String status) {
        char s1 = status.charAt(0);
        char s2 = status.charAt(1);
        boolean numeric = isDigit(s1) && isDigit(s2);
        if (!numeric || s1 == '9') {
            long bin = ebcdic(s2);
            r.displays.add("FILE STATUS IS: NNNN" + s1 + padNum(bin, 3));
        } else {
            r.displays.add("FILE STATUS IS: NNNN" + "00" + s1 + s2);
        }
    }

    // ------------------------------------------------------------------
    // Search helpers
    // ------------------------------------------------------------------

    private static int findXref(CardXrefRecord[] f, String key) {
        for (int i = 0; i < f.length; i++) {
            if (f[i].xrefCardNum.equals(key)) {
                return i;
            }
        }
        return -1;
    }

    private static int findAccount(AccountRecord[] f, long key) {
        for (int i = 0; i < f.length; i++) {
            if (f[i].acctId == key) {
                return i;
            }
        }
        return -1;
    }

    private static int findTcatbal(List<TranCatBalRecord> f, long acct, String type, long cd) {
        for (int i = 0; i < f.size(); i++) {
            TranCatBalRecord t = f.get(i);
            if (t.trancatAcctId == acct && t.trancatTypeCd.equals(type) && t.trancatCd == cd) {
                return i;
            }
        }
        return -1;
    }

    private static int findKey(List<String> keys, String key) {
        for (int i = 0; i < keys.size(); i++) {
            if (keys.get(i).equals(key)) {
                return i;
            }
        }
        return -1;
    }

    // ------------------------------------------------------------------
    // Copy helpers
    // ------------------------------------------------------------------

    private static void assignXref(CardXrefRecord dst, CardXrefRecord src) {
        dst.xrefCardNum = src.xrefCardNum;
        dst.xrefCustId = src.xrefCustId;
        dst.xrefAcctId = src.xrefAcctId;
        dst.filler1 = src.filler1;
    }

    private static void assignAccount(AccountRecord dst, AccountRecord src) {
        dst.acctId = src.acctId;
        dst.acctActiveStatus = src.acctActiveStatus;
        dst.acctCurrBal = src.acctCurrBal;
        dst.acctCreditLimit = src.acctCreditLimit;
        dst.acctCashCreditLimit = src.acctCashCreditLimit;
        dst.acctOpenDate = src.acctOpenDate;
        dst.acctExpiraionDate = src.acctExpiraionDate;
        dst.acctReissueDate = src.acctReissueDate;
        dst.acctCurrCycCredit = src.acctCurrCycCredit;
        dst.acctCurrCycDebit = src.acctCurrCycDebit;
        dst.acctAddrZip = src.acctAddrZip;
        dst.acctGroupId = src.acctGroupId;
        dst.filler1 = src.filler1;
    }

    private static AccountRecord copyAccount(AccountRecord a) {
        return new AccountRecord(a.acctId, a.acctActiveStatus, a.acctCurrBal, a.acctCreditLimit,
                a.acctCashCreditLimit, a.acctOpenDate, a.acctExpiraionDate, a.acctReissueDate,
                a.acctCurrCycCredit, a.acctCurrCycDebit, a.acctAddrZip, a.acctGroupId,
                a.filler1);
    }

    private static void assignTcat(TranCatBalRecord dst, TranCatBalRecord src) {
        dst.trancatAcctId = src.trancatAcctId;
        dst.trancatTypeCd = src.trancatTypeCd;
        dst.trancatCd = src.trancatCd;
        dst.tranCatBal = src.tranCatBal;
        dst.filler1 = src.filler1;
    }

    private static TranCatBalRecord copyTcat(TranCatBalRecord t) {
        return new TranCatBalRecord(t.trancatAcctId, t.trancatTypeCd, t.trancatCd, t.tranCatBal,
                t.filler1);
    }

    private static TranRecord copyTran(TranRecord t) {
        return new TranRecord(t.tranId, t.tranTypeCd, t.tranCatCd, t.tranSource, t.tranDesc,
                t.tranAmt, t.tranMerchantId, t.tranMerchantName, t.tranMerchantCity,
                t.tranMerchantZip, t.tranCardNum, t.tranOrigTs, t.tranProcTs, t.filler1);
    }

    // ------------------------------------------------------------------
    // Formatting helpers
    // ------------------------------------------------------------------

    private static String db2Timestamp(String clock) {
        StringBuilder sb = new StringBuilder();
        sb.append(clock.substring(0, 4));
        sb.append('-');
        sb.append(clock.substring(4, 6));
        sb.append('-');
        sb.append(clock.substring(6, 8));
        sb.append('-');
        sb.append(clock.substring(8, 10));
        sb.append('.');
        sb.append(clock.substring(10, 12));
        sb.append('.');
        sb.append(clock.substring(12, 14));
        sb.append('.');
        sb.append(clock.substring(14, 16));
        sb.append("0000");
        return sb.toString();
    }

    private static String dalytranText(DalytranRecord d) {
        StringBuilder sb = new StringBuilder();
        sb.append(fit(d.dalytranId, 16));
        sb.append(fit(d.dalytranTypeCd, 2));
        sb.append(padNum(d.dalytranCatCd, 4));
        sb.append(fit(d.dalytranSource, 10));
        sb.append(fit(d.dalytranDesc, 100));
        sb.append(zonedSigned(d.dalytranAmt, 11));
        sb.append(padNum(d.dalytranMerchantId, 9));
        sb.append(fit(d.dalytranMerchantName, 50));
        sb.append(fit(d.dalytranMerchantCity, 50));
        sb.append(fit(d.dalytranMerchantZip, 10));
        sb.append(fit(d.dalytranCardNum, 16));
        sb.append(fit(d.dalytranOrigTs, 26));
        sb.append(fit(d.dalytranProcTs, 26));
        sb.append(fit(d.filler1, 20));
        return sb.toString();
    }

    private static String spaces(int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            sb.append(' ');
        }
        return sb.toString();
    }

    private static String fit(String s, int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            if (s != null && i < s.length()) {
                sb.append(s.charAt(i));
            } else {
                sb.append(' ');
            }
        }
        return sb.toString();
    }

    private static String padNum(long v, int n) {
        long a = v < 0 ? -v : v;
        StringBuilder rev = new StringBuilder();
        for (int i = 0; i < n; i++) {
            rev.append((char) ('0' + (a % 10)));
            a = a / 10;
        }
        StringBuilder sb = new StringBuilder();
        for (int i = n - 1; i >= 0; i--) {
            sb.append(rev.charAt(i));
        }
        return sb.toString();
    }

    private static String zonedSigned(long v, int n) {
        String digits = padNum(v, n);
        int last = digits.charAt(n - 1) - '0';
        char over;
        if (v < 0) {
            over = "}JKLMNOPQR".charAt(last);
        } else {
            over = "{ABCDEFGHI".charAt(last);
        }
        StringBuilder sb = new StringBuilder();
        sb.append(digits.substring(0, n - 1));
        sb.append(over);
        return sb.toString();
    }

    private static boolean isDigit(char c) {
        return c >= '0' && c <= '9';
    }

    // ------------------------------------------------------------------
    // EBCDIC collation (CP037)
    // ------------------------------------------------------------------

    // CP037: charAt(e) is the Unicode character of EBCDIC byte e.
    private static final String CP037 =
        "\u0000\u0001\u0002\u0003\u009C\t\u0086\u007F\u0097\u008D\u008E\u000B\f\r\u000E\u000F"
      + "\u0010\u0011\u0012\u0013\u009D\u0085\b\u0087\u0018\u0019\u0092\u008F\u001C\u001D\u001E\u001F"
      + "\u0080\u0081\u0082\u0083\u0084\n\u0017\u001B\u0088\u0089\u008A\u008B\u008C\u0005\u0006\u0007"
      + "\u0090\u0091\u0016\u0093\u0094\u0095\u0096\u0004\u0098\u0099\u009A\u009B\u0014\u0015\u009E\u001A"
      + " \u00A0\u00E2\u00E4\u00E0\u00E1\u00E3\u00E5\u00E7\u00F1\u00A2.<(+|"
      + "&\u00E9\u00EA\u00EB\u00E8\u00ED\u00EE\u00EF\u00EC\u00DF!$*);\u00AC"
      + "-/\u00C2\u00C4\u00C0\u00C1\u00C3\u00C5\u00C7\u00D1\u00A6,%_>?"
      + "\u00F8\u00C9\u00CA\u00CB\u00C8\u00CD\u00CE\u00CF\u00CC`:#@'=\""
      + "\u00D8abcdefghi\u00AB\u00BB\u00F0\u00FD\u00FE\u00B1"
      + "\u00B0jklmnopqr\u00AA\u00BA\u00E6\u00B8\u00C6\u00A4"
      + "\u00B5~stuvwxyz\u00A1\u00BF\u00D0\u00DD\u00DE\u00AE"
      + "^\u00A3\u00A5\u00B7\u00A9\u00A7\u00B6\u00BC\u00BD\u00BE[]\u00AF\u00A8\u00B4\u00D7"
      + "{ABCDEFGHI\u00AD\u00F4\u00F6\u00F2\u00F3\u00F5"
      + "}JKLMNOPQR\u00B9\u00FB\u00FC\u00F9\u00FA\u00FF"
      + "\\\u00F7STUVWXYZ\u00B2\u00D4\u00D6\u00D2\u00D3\u00D5"
      + "0123456789\u00B3\u00DB\u00DC\u00D9\u00DA\u009F";

    private static int compareEbcdic(String a, String b) {
        int n = a.length() > b.length() ? a.length() : b.length();
        for (int i = 0; i < n; i++) {
            char ca = i < a.length() ? a.charAt(i) : ' ';
            char cb = i < b.length() ? b.charAt(i) : ' ';
            int ea = ebcdic(ca);
            int eb = ebcdic(cb);
            if (ea < eb) {
                return -1;
            }
            if (ea > eb) {
                return 1;
            }
        }
        return 0;
    }

    private static int ebcdic(char c) {
        for (int i = 0; i < 256; i++) {
            if (CP037.charAt(i) == c) {
                return i;
            }
        }
        return (int) c;
    }
}