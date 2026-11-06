public final class Cbact04c {

    public static final class TranCatBalRecord {
        public long trancatAcctId;
        public String trancatTypeCd;
        public long trancatCd;
        public long tranCatBal;
        public String filler1;

        public TranCatBalRecord(long trancatAcctId, String trancatTypeCd, long trancatCd, long tranCatBal,
                String filler1) {
            this.trancatAcctId = trancatAcctId;
            this.trancatTypeCd = trancatTypeCd;
            this.trancatCd = trancatCd;
            this.tranCatBal = tranCatBal;
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

    public static final class DisGroupRecord {
        public String disAcctGroupId;
        public String disTranTypeCd;
        public long disTranCatCd;
        public long disIntRate;
        public String filler1;

        public DisGroupRecord(String disAcctGroupId, String disTranTypeCd, long disTranCatCd, long disIntRate,
                String filler1) {
            this.disAcctGroupId = disAcctGroupId;
            this.disTranTypeCd = disTranTypeCd;
            this.disTranCatCd = disTranCatCd;
            this.disIntRate = disIntRate;
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

        public AccountRecord(long acctId, String acctActiveStatus, long acctCurrBal, long acctCreditLimit,
                long acctCashCreditLimit, String acctOpenDate, String acctExpiraionDate, String acctReissueDate,
                long acctCurrCycCredit, long acctCurrCycDebit, String acctAddrZip, String acctGroupId,
                String filler1) {
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

        public TranRecord(String tranId, String tranTypeCd, long tranCatCd, String tranSource, String tranDesc,
                long tranAmt, long tranMerchantId, String tranMerchantName, String tranMerchantCity,
                String tranMerchantZip, String tranCardNum, String tranOrigTs, String tranProcTs,
                String filler1) {
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

    public static final class ExternalParms {
        public long parmLength;
        public String parmDate;

        public ExternalParms(long parmLength, String parmDate) {
            this.parmLength = parmLength;
            this.parmDate = parmDate;
        }
    }

    public static final class Result {
        public java.util.List<String> displays = new java.util.ArrayList<String>();
        public java.util.List<TranRecord> transactFileWrites = new java.util.ArrayList<TranRecord>();
        public java.util.List<AccountRecord> accountFileRewrites = new java.util.ArrayList<AccountRecord>();
        public boolean abended;
    }

    public static Result run(TranCatBalRecord[] tcatbalFile, CardXrefRecord[] xrefFile,
            AccountRecord[] accountFile, DisGroupRecord[] discgrpFile, ExternalParms externalParms,
            String clock) {
        Result r = new Result();
        r.displays.add("START OF EXECUTION OF PROGRAM CBACT04C");
        // all OPENs succeed

        int tcatLen = tcatbalFile == null ? 0 : tcatbalFile.length;
        int xrefLen = xrefFile == null ? 0 : xrefFile.length;
        int discLen = discgrpFile == null ? 0 : discgrpFile.length;
        int acctLen = accountFile == null ? 0 : accountFile.length;
        AccountRecord[] accts = new AccountRecord[acctLen];
        for (int i = 0; i < acctLen; i++) {
            accts[i] = copyAcct(accountFile[i]);
        }

        TranCatBalRecord tcb = new TranCatBalRecord(0L, spaces(2), 0L, 0L, spaces(22));
        CardXrefRecord xref = new CardXrefRecord(spaces(16), 0L, 0L, spaces(14));
        DisGroupRecord dis = new DisGroupRecord(spaces(10), spaces(2), 0L, 0L, spaces(28));
        AccountRecord acct = new AccountRecord(0L, spaces(1), 0L, 0L, 0L, spaces(10), spaces(10), spaces(10),
                0L, 0L, spaces(10), spaces(10), spaces(178));
        TranRecord tran = new TranRecord(spaces(16), spaces(2), 0L, spaces(10), spaces(100), 0L, 0L,
                spaces(50), spaces(50), spaces(10), spaces(16), spaces(26), spaces(26), spaces(20));

        long fdAcctId = 0L;
        long fdXrefAcctId = 0L;
        String fdDisAcctGroupId = spaces(10);
        String fdDisTranTypeCd = spaces(2);
        long fdDisTranCatCd = 0L;

        String wsLastAcctNum = spaces(11);
        long wsMonthlyInt = 0L;
        long wsTotalInt = 0L;
        boolean firstTime = true;
        long recordCount = 0L;
        long tranidSuffix = 0L;

        String parmDate = fixLen(externalParms == null ? null : externalParms.parmDate, 10);
        String clk = fixLen(clock, 21);

        boolean eof = false;
        int tcatPos = 0;
        while (!eof) {
            // 1000-TCATBALF-GET-NEXT
            if (tcatPos < tcatLen) {
                tcb = copyTcb(tcatbalFile[tcatPos]);
                tcatPos++;
            } else {
                eof = true;
            }
            if (eof) {
                break;
            }
            recordCount = (recordCount + 1L) % 1000000000L;
            r.displays.add(displayTcb(tcb));
            if (!fmtU(tcb.trancatAcctId, 11).equals(wsLastAcctNum)) {
                if (!firstTime) {
                    // 1050-UPDATE-ACCOUNT
                    acct.acctCurrBal = trunc(acct.acctCurrBal + wsTotalInt, 12);
                    acct.acctCurrCycCredit = 0L;
                    acct.acctCurrCycDebit = 0L;
                    fdAcctId = acct.acctId;
                    int ri = findAcct(accts, fdAcctId);
                    if (ri >= 0) {
                        accts[ri] = copyAcct(acct);
                        r.accountFileRewrites.add(copyAcct(acct));
                    } else {
                        r.displays.add("ERROR RE-WRITING ACCOUNT FILE");
                        r.displays.add(statusLine("23"));
                        return abend(r);
                    }
                } else {
                    firstTime = false;
                }
                wsTotalInt = 0L;
                wsLastAcctNum = fmtU(tcb.trancatAcctId, 11);
                fdAcctId = tcb.trancatAcctId;
                // 1100-GET-ACCT-DATA
                int ai = findAcct(accts, fdAcctId);
                if (ai >= 0) {
                    acct = copyAcct(accts[ai]);
                } else {
                    r.displays.add("ACCOUNT NOT FOUND: " + fmtU(fdAcctId, 11));
                    r.displays.add("ERROR READING ACCOUNT FILE");
                    r.displays.add(statusLine("23"));
                    return abend(r);
                }
                fdXrefAcctId = tcb.trancatAcctId;
                // 1110-GET-XREF-DATA
                int xi = -1;
                for (int i = 0; i < xrefLen; i++) {
                    if (xrefFile[i].xrefAcctId == fdXrefAcctId) {
                        xi = i;
                        break;
                    }
                }
                if (xi >= 0) {
                    xref = copyXref(xrefFile[xi]);
                } else {
                    r.displays.add("ACCOUNT NOT FOUND: " + fmtU(fdXrefAcctId, 11));
                    r.displays.add("ERROR READING XREF FILE");
                    r.displays.add(statusLine("23"));
                    return abend(r);
                }
            }
            fdDisAcctGroupId = acct.acctGroupId;
            fdDisTranCatCd = tcb.trancatCd;
            fdDisTranTypeCd = tcb.trancatTypeCd;
            // 1200-GET-INTEREST-RATE
            int di = findDisc(discgrpFile, discLen, fdDisAcctGroupId, fdDisTranTypeCd, fdDisTranCatCd);
            if (di >= 0) {
                dis = copyDis(discgrpFile[di]);
            } else {
                r.displays.add("DISCLOSURE GROUP RECORD MISSING");
                r.displays.add("TRY WITH DEFAULT GROUP CODE");
                fdDisAcctGroupId = "DEFAULT   ";
                // 1200-A-GET-DEFAULT-INT-RATE
                int di2 = findDisc(discgrpFile, discLen, fdDisAcctGroupId, fdDisTranTypeCd, fdDisTranCatCd);
                if (di2 >= 0) {
                    dis = copyDis(discgrpFile[di2]);
                } else {
                    r.displays.add("ERROR READING DEFAULT DISCLOSURE GROUP");
                    r.displays.add(statusLine("23"));
                    return abend(r);
                }
            }
            if (dis.disIntRate != 0L) {
                // 1300-COMPUTE-INTEREST
                long prod = tcb.tranCatBal * dis.disIntRate;
                wsMonthlyInt = trunc(prod / 120000L, 11);
                wsTotalInt = trunc(wsTotalInt + wsMonthlyInt, 11);
                // 1300-B-WRITE-TX
                tranidSuffix = (tranidSuffix + 1L) % 1000000L;
                tran.tranId = parmDate + fmtU(tranidSuffix, 6);
                tran.tranTypeCd = "01";
                tran.tranCatCd = 5L;
                tran.tranSource = "System    ";
                String desc = "Int. for a/c " + fmtU(acct.acctId, 11);
                tran.tranDesc = desc + tran.tranDesc.substring(desc.length());
                tran.tranAmt = wsMonthlyInt;
                tran.tranMerchantId = 0L;
                tran.tranMerchantName = spaces(50);
                tran.tranMerchantCity = spaces(50);
                tran.tranMerchantZip = spaces(10);
                tran.tranCardNum = xref.xrefCardNum;
                String ts = clk.substring(0, 4) + "-" + clk.substring(4, 6) + "-" + clk.substring(6, 8) + "-"
                        + clk.substring(8, 10) + "." + clk.substring(10, 12) + "." + clk.substring(12, 14) + "."
                        + clk.substring(14, 16) + "0000";
                tran.tranOrigTs = ts;
                tran.tranProcTs = ts;
                r.transactFileWrites.add(copyTran(tran));
                // 1400-COMPUTE-FEES: nothing
            }
        }

        // all CLOSEs succeed
        r.displays.add("END OF EXECUTION OF PROGRAM CBACT04C");
        return r;
    }

    private static Result abend(Result r) {
        r.displays.add("ABENDING PROGRAM");
        r.abended = true;
        return r;
    }

    private static String statusLine(String status) {
        return "FILE STATUS IS: NNNN" + "00" + status;
    }

    private static int findAcct(AccountRecord[] accts, long key) {
        for (int i = 0; i < accts.length; i++) {
            if (accts[i].acctId == key) {
                return i;
            }
        }
        return -1;
    }

    private static int findDisc(DisGroupRecord[] file, int len, String grp, String type, long cat) {
        for (int i = 0; i < len; i++) {
            DisGroupRecord d = file[i];
            if (d.disAcctGroupId.equals(grp) && d.disTranTypeCd.equals(type) && d.disTranCatCd == cat) {
                return i;
            }
        }
        return -1;
    }

    private static String displayTcb(TranCatBalRecord t) {
        StringBuilder sb = new StringBuilder();
        sb.append(fmtU(t.trancatAcctId, 11));
        sb.append(t.trancatTypeCd);
        sb.append(fmtU(t.trancatCd, 4));
        sb.append(fmtZoned(t.tranCatBal, 11));
        sb.append(t.filler1);
        return sb.toString();
    }

    private static long pow10(int n) {
        long p = 1L;
        for (int i = 0; i < n; i++) {
            p = p * 10L;
        }
        return p;
    }

    private static long trunc(long v, int digits) {
        return v % pow10(digits);
    }

    private static String fmtU(long v, int n) {
        long a = v < 0 ? -v : v;
        a = a % pow10(n);
        char[] c = new char[n];
        for (int i = n - 1; i >= 0; i--) {
            c[i] = (char) ('0' + (int) (a % 10L));
            a = a / 10L;
        }
        return new String(c);
    }

    private static String fmtZoned(long v, int n) {
        String digits = fmtU(v, n);
        int last = digits.charAt(n - 1) - '0';
        char sc;
        if (v < 0) {
            sc = "}JKLMNOPQR".charAt(last);
        } else {
            sc = "{ABCDEFGHI".charAt(last);
        }
        return digits.substring(0, n - 1) + sc;
    }

    private static String spaces(int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            sb.append(' ');
        }
        return sb.toString();
    }

    private static String fixLen(String s, int n) {
        if (s == null) {
            return spaces(n);
        }
        if (s.length() >= n) {
            return s.substring(0, n);
        }
        StringBuilder sb = new StringBuilder(s);
        while (sb.length() < n) {
            sb.append(' ');
        }
        return sb.toString();
    }

    private static TranCatBalRecord copyTcb(TranCatBalRecord t) {
        return new TranCatBalRecord(t.trancatAcctId, t.trancatTypeCd, t.trancatCd, t.tranCatBal, t.filler1);
    }

    private static CardXrefRecord copyXref(CardXrefRecord x) {
        return new CardXrefRecord(x.xrefCardNum, x.xrefCustId, x.xrefAcctId, x.filler1);
    }

    private static DisGroupRecord copyDis(DisGroupRecord d) {
        return new DisGroupRecord(d.disAcctGroupId, d.disTranTypeCd, d.disTranCatCd, d.disIntRate, d.filler1);
    }

    private static AccountRecord copyAcct(AccountRecord a) {
        return new AccountRecord(a.acctId, a.acctActiveStatus, a.acctCurrBal, a.acctCreditLimit,
                a.acctCashCreditLimit, a.acctOpenDate, a.acctExpiraionDate, a.acctReissueDate,
                a.acctCurrCycCredit, a.acctCurrCycDebit, a.acctAddrZip, a.acctGroupId, a.filler1);
    }

    private static TranRecord copyTran(TranRecord t) {
        return new TranRecord(t.tranId, t.tranTypeCd, t.tranCatCd, t.tranSource, t.tranDesc, t.tranAmt,
                t.tranMerchantId, t.tranMerchantName, t.tranMerchantCity, t.tranMerchantZip, t.tranCardNum,
                t.tranOrigTs, t.tranProcTs, t.filler1);
    }
}