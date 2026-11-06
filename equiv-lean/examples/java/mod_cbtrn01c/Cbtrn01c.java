import java.util.ArrayList;
import java.util.List;

public final class Cbtrn01c {

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
                              String dalytranCardNum, String dalytranOrigTs, String dalytranProcTs,
                              String filler1) {
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

    public static final class FdCustfileRec {
        public long fdCustId;
        public String fdCustData;

        public FdCustfileRec(long fdCustId, String fdCustData) {
            this.fdCustId = fdCustId;
            this.fdCustData = fdCustData;
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

    public static final class FdCardfileRec {
        public String fdCardNum;
        public String fdCardData;

        public FdCardfileRec(String fdCardNum, String fdCardData) {
            this.fdCardNum = fdCardNum;
            this.fdCardData = fdCardData;
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

    public static final class FdTranfileRec {
        public String fdTransId;
        public String fdAcctData;

        public FdTranfileRec(String fdTransId, String fdAcctData) {
            this.fdTransId = fdTransId;
            this.fdAcctData = fdAcctData;
        }
    }

    public static final class Result {
        public List<String> displays = new ArrayList<String>();
        public boolean abended = false;
    }

    public static Result run(DalytranRecord[] dalytranFile,
                             FdCustfileRec[] customerFile,
                             CardXrefRecord[] xrefFile,
                             FdCardfileRec[] cardFile,
                             AccountRecord[] accountFile,
                             FdTranfileRec[] transactFile) {
        Result r = new Result();
        List<String> d = r.displays;

        d.add("START OF EXECUTION OF PROGRAM CBTRN01C");
        // All OPENs succeed (status '00').

        // DALYTRAN-RECORD initial contents (INITIALIZE semantics)
        DalytranRecord dal = new DalytranRecord(spaces(16), spaces(2), 0L, spaces(10), spaces(100),
                0L, 0L, spaces(50), spaces(50), spaces(10), spaces(16), spaces(26), spaces(26),
                spaces(20));

        // CARD-XREF-RECORD working fields
        String xrefCardNum = spaces(16);
        long xrefCustId = 0L;
        long xrefAcctId = 0L;
        // ACCOUNT-RECORD working field used
        long acctId = 0L;

        int dalPos = 0;
        boolean dalEofHit = false;
        boolean endOfFile = false; // END-OF-DAILY-TRANS-FILE = 'Y'

        while (!endOfFile) {
            // 1000-DALYTRAN-GET-NEXT
            String status;
            if (dalPos < dalytranFile.length) {
                dal = dalytranFile[dalPos];
                dalPos++;
                status = "00";
            } else if (!dalEofHit) {
                dalEofHit = true;
                status = "10";
            } else {
                status = "46";
            }
            if (status.equals("00")) {
                // continue
            } else if (status.equals("10")) {
                endOfFile = true;
            } else {
                d.add("ERROR READING DAILY TRANSACTION FILE");
                displayIoStatus(d, status);
                d.add("ABENDING PROGRAM");
                r.abended = true;
                return r;
            }

            if (!endOfFile) {
                d.add(formatDalytran(dal));
            }

            long wsXrefReadStatus = 0;
            xrefCardNum = dal.dalytranCardNum;

            // 2000-LOOKUP-XREF
            CardXrefRecord found = null;
            for (int i = 0; i < xrefFile.length; i++) {
                if (xrefFile[i].xrefCardNum.equals(xrefCardNum)) {
                    found = xrefFile[i];
                    break;
                }
            }
            if (found == null) {
                d.add("INVALID CARD NUMBER FOR XREF");
                wsXrefReadStatus = 4;
            } else {
                xrefCardNum = found.xrefCardNum;
                xrefCustId = found.xrefCustId;
                xrefAcctId = found.xrefAcctId;
                d.add("SUCCESSFUL READ OF XREF");
                d.add("CARD NUMBER: " + xrefCardNum);
                d.add("ACCOUNT ID : " + digits(xrefAcctId, 11));
                d.add("CUSTOMER ID: " + digits(xrefCustId, 9));
            }

            if (wsXrefReadStatus == 0) {
                long wsAcctReadStatus = 0;
                acctId = xrefAcctId;
                // 3000-READ-ACCOUNT
                AccountRecord acct = null;
                for (int i = 0; i < accountFile.length; i++) {
                    if (accountFile[i].acctId == acctId) {
                        acct = accountFile[i];
                        break;
                    }
                }
                if (acct == null) {
                    d.add("INVALID ACCOUNT NUMBER FOUND");
                    wsAcctReadStatus = 4;
                } else {
                    acctId = acct.acctId;
                    d.add("SUCCESSFUL READ OF ACCOUNT FILE");
                }
                if (wsAcctReadStatus != 0) {
                    d.add("ACCOUNT " + digits(acctId, 11) + " NOT FOUND");
                }
            } else {
                d.add("CARD NUMBER " + dal.dalytranCardNum
                        + " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-"
                        + dal.dalytranId);
            }
        }

        // All CLOSEs succeed (status '00').
        d.add("END OF EXECUTION OF PROGRAM CBTRN01C");
        return r;
    }

    private static void displayIoStatus(List<String> d, String ioStatus) {
        char s1 = ioStatus.charAt(0);
        char s2 = ioStatus.charAt(1);
        boolean numeric = s1 >= '0' && s1 <= '9' && s2 >= '0' && s2 <= '9';
        if (!numeric || s1 == '9') {
            int bin = ((int) s2) & 0xFF;
            d.add("FILE STATUS IS: NNNN" + s1 + digits(bin, 3));
        } else {
            d.add("FILE STATUS IS: NNNN" + "00" + ioStatus);
        }
    }

    private static String formatDalytran(DalytranRecord x) {
        StringBuilder sb = new StringBuilder();
        sb.append(x.dalytranId);
        sb.append(x.dalytranTypeCd);
        sb.append(digits(x.dalytranCatCd, 4));
        sb.append(x.dalytranSource);
        sb.append(x.dalytranDesc);
        sb.append(signedZoned(x.dalytranAmt, 11));
        sb.append(digits(x.dalytranMerchantId, 9));
        sb.append(x.dalytranMerchantName);
        sb.append(x.dalytranMerchantCity);
        sb.append(x.dalytranMerchantZip);
        sb.append(x.dalytranCardNum);
        sb.append(x.dalytranOrigTs);
        sb.append(x.dalytranProcTs);
        sb.append(x.filler1);
        return sb.toString();
    }

    private static String spaces(int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            sb.append(' ');
        }
        return sb.toString();
    }

    private static String digits(long v, int n) {
        if (v < 0) {
            v = -v;
        }
        char[] c = new char[n];
        for (int i = n - 1; i >= 0; i--) {
            c[i] = (char) ('0' + (int) (v % 10));
            v = v / 10;
        }
        return new String(c);
    }

    private static String signedZoned(long v, int n) {
        boolean neg = v < 0;
        String s = digits(v, n);
        int last = s.charAt(n - 1) - '0';
        char lc;
        if (neg) {
            lc = (last == 0) ? '}' : (char) ('J' + last - 1);
        } else {
            lc = (last == 0) ? '{' : (char) ('A' + last - 1);
        }
        return s.substring(0, n - 1) + lc;
    }
}