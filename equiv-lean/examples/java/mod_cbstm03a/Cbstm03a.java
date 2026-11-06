import java.util.ArrayList;
import java.util.List;

public final class Cbstm03a {

    public static final class TrnxRecord {
        public String trnxCardNum;
        public String trnxId;
        public String trnxTypeCd;
        public long trnxCatCd;
        public String trnxSource;
        public String trnxDesc;
        public long trnxAmt;
        public long trnxMerchantId;
        public String trnxMerchantName;
        public String trnxMerchantCity;
        public String trnxMerchantZip;
        public String trnxOrigTs;
        public String trnxProcTs;
        public String filler1;

        public TrnxRecord(String trnxCardNum, String trnxId, String trnxTypeCd, long trnxCatCd,
                          String trnxSource, String trnxDesc, long trnxAmt, long trnxMerchantId,
                          String trnxMerchantName, String trnxMerchantCity, String trnxMerchantZip,
                          String trnxOrigTs, String trnxProcTs, String filler1) {
            this.trnxCardNum = trnxCardNum;
            this.trnxId = trnxId;
            this.trnxTypeCd = trnxTypeCd;
            this.trnxCatCd = trnxCatCd;
            this.trnxSource = trnxSource;
            this.trnxDesc = trnxDesc;
            this.trnxAmt = trnxAmt;
            this.trnxMerchantId = trnxMerchantId;
            this.trnxMerchantName = trnxMerchantName;
            this.trnxMerchantCity = trnxMerchantCity;
            this.trnxMerchantZip = trnxMerchantZip;
            this.trnxOrigTs = trnxOrigTs;
            this.trnxProcTs = trnxProcTs;
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

    public static final class CustomerRecord {
        public long custId;
        public String custFirstName;
        public String custMiddleName;
        public String custLastName;
        public String custAddrLine1;
        public String custAddrLine2;
        public String custAddrLine3;
        public String custAddrStateCd;
        public String custAddrCountryCd;
        public String custAddrZip;
        public String custPhoneNum1;
        public String custPhoneNum2;
        public long custSsn;
        public String custGovtIssuedId;
        public String custDobYyyymmdd;
        public String custEftAccountId;
        public String custPriCardHolderInd;
        public long custFicoCreditScore;
        public String filler1;

        public CustomerRecord(long custId, String custFirstName, String custMiddleName, String custLastName,
                              String custAddrLine1, String custAddrLine2, String custAddrLine3,
                              String custAddrStateCd, String custAddrCountryCd, String custAddrZip,
                              String custPhoneNum1, String custPhoneNum2, long custSsn,
                              String custGovtIssuedId, String custDobYyyymmdd, String custEftAccountId,
                              String custPriCardHolderInd, long custFicoCreditScore, String filler1) {
            this.custId = custId;
            this.custFirstName = custFirstName;
            this.custMiddleName = custMiddleName;
            this.custLastName = custLastName;
            this.custAddrLine1 = custAddrLine1;
            this.custAddrLine2 = custAddrLine2;
            this.custAddrLine3 = custAddrLine3;
            this.custAddrStateCd = custAddrStateCd;
            this.custAddrCountryCd = custAddrCountryCd;
            this.custAddrZip = custAddrZip;
            this.custPhoneNum1 = custPhoneNum1;
            this.custPhoneNum2 = custPhoneNum2;
            this.custSsn = custSsn;
            this.custGovtIssuedId = custGovtIssuedId;
            this.custDobYyyymmdd = custDobYyyymmdd;
            this.custEftAccountId = custEftAccountId;
            this.custPriCardHolderInd = custPriCardHolderInd;
            this.custFicoCreditScore = custFicoCreditScore;
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

    public static final class Result {
        public List<String> displays = new ArrayList<String>();
        public List<String> stmtFileWrites = new ArrayList<String>();
        public List<String> htmlFileWrites = new ArrayList<String>();
        public boolean abended;
    }

    private static final int CARD_SZ = 3356;
    private static final int TRAN_SZ = 334;
    private static final int CARD_MAX = 51;
    private static final long MEM_SZ = (long) CARD_MAX * CARD_SZ;

    private static final String L01 = "<!DOCTYPE html>";
    private static final String L02 = "<html lang=\"en\">";
    private static final String L03 = "<head>";
    private static final String L04 = "<meta charset=\"utf-8\">";
    private static final String L05 = "<title>HTML Table Layout</title>";
    private static final String L06 = "</head>";
    private static final String L07 = "<body style=\"margin:0px;\">";
    private static final String L08 = "<table  align=\"center\" frame=\"box\" style=\"width:70%; font:12px Segoe UI,sans-serif;\">";
    private static final String LTRS = "<tr>";
    private static final String LTRE = "</tr>";
    private static final String LTDE = "</td>";
    private static final String L10 = "<td colspan=\"3\" style=\"padding:0px 5px;background-color:#1d1d96b3;\">";
    private static final String L15 = "<td colspan=\"3\" style=\"padding:0px 5px;background-color:#FFAF33;\">";
    private static final String L16 = "<p style=\"font-size:16px\">Bank of XYZ</p>";
    private static final String L17 = "<p>410 Terry Ave N</p>";
    private static final String L18 = "<p>Seattle WA 99999</p>";
    private static final String L22_35 = "<td colspan=\"3\" style=\"padding:0px 5px;background-color:#f2f2f2;\">";
    private static final String L30_42 = "<td colspan=\"3\" style=\"padding:0px 5px;background-color:#33FFD1; text-align:center;\">";
    private static final String L31 = "<p style=\"font-size:16px\">Basic Details</p>";
    private static final String L43 = "<p style=\"font-size:16px\">Transaction Summary</p>";
    private static final String L47 = "<td style=\"width:25%; padding:0px 5px; background-color:#33FF5E; text-align:left;\">";
    private static final String L48 = "<p style=\"font-size:16px\">Tran ID</p>";
    private static final String L50 = "<td style=\"width:55%; padding:0px 5px; background-color:#33FF5E; text-align:left;\">";
    private static final String L51 = "<p style=\"font-size:16px\">Tran Details</p>";
    private static final String L53 = "<td style=\"width:20%; padding:0px 5px; background-color:#33FF5E; text-align:right;\">";
    private static final String L54 = "<p style=\"font-size:16px\">Amount</p>";
    private static final String L58 = "<td style=\"width:25%; padding:0px 5px; background-color:#f2f2f2; text-align:left;\">";
    private static final String L61 = "<td style=\"width:55%; padding:0px 5px; background-color:#f2f2f2; text-align:left;\">";
    private static final String L64 = "<td style=\"width:20%; padding:0px 5px; background-color:#f2f2f2; text-align:right;\">";
    private static final String L75 = "<h3>End of Statement</h3>";
    private static final String L78 = "</table>";
    private static final String L79 = "</body>";
    private static final String L80 = "</html>";

    // CP037: EBCDIC code -> Unicode
    private static final int[] CP037 = {
        0x00, 0x01, 0x02, 0x03, 0x9C, 0x09, 0x86, 0x7F, 0x97, 0x8D, 0x8E, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x9D, 0x85, 0x08, 0x87, 0x18, 0x19, 0x92, 0x8F, 0x1C, 0x1D, 0x1E, 0x1F,
        0x80, 0x81, 0x82, 0x83, 0x84, 0x0A, 0x17, 0x1B, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x05, 0x06, 0x07,
        0x90, 0x91, 0x16, 0x93, 0x94, 0x95, 0x96, 0x04, 0x98, 0x99, 0x9A, 0x9B, 0x14, 0x15, 0x9E, 0x1A,
        0x20, 0xA0, 0xE2, 0xE4, 0xE0, 0xE1, 0xE3, 0xE5, 0xE7, 0xF1, 0xA2, 0x2E, 0x3C, 0x28, 0x2B, 0x7C,
        0x26, 0xE9, 0xEA, 0xEB, 0xE8, 0xED, 0xEE, 0xEF, 0xEC, 0xDF, 0x21, 0x24, 0x2A, 0x29, 0x3B, 0xAC,
        0x2D, 0x2F, 0xC2, 0xC4, 0xC0, 0xC1, 0xC3, 0xC5, 0xC7, 0xD1, 0xA6, 0x2C, 0x25, 0x5F, 0x3E, 0x3F,
        0xF8, 0xC9, 0xCA, 0xCB, 0xC8, 0xCD, 0xCE, 0xCF, 0xCC, 0x60, 0x3A, 0x23, 0x40, 0x27, 0x3D, 0x22,
        0xD8, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xAB, 0xBB, 0xF0, 0xFD, 0xFE, 0xB1,
        0xB0, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0xAA, 0xBA, 0xE6, 0xB8, 0xC6, 0xA4,
        0xB5, 0x7E, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0xA1, 0xBF, 0xD0, 0xDD, 0xDE, 0xAE,
        0x5E, 0xA3, 0xA5, 0xB7, 0xA9, 0xA7, 0xB6, 0xBC, 0xBD, 0xBE, 0x5B, 0x5D, 0xAF, 0xA8, 0xB4, 0xD7,
        0x7B, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0xAD, 0xF4, 0xF6, 0xF2, 0xF3, 0xF5,
        0x7D, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0xB9, 0xFB, 0xFC, 0xF9, 0xFA, 0xFF,
        0x5C, 0xF7, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0xB2, 0xD4, 0xD6, 0xD2, 0xD3, 0xD5,
        0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0xB3, 0xDB, 0xDC, 0xD9, 0xDA, 0x9F
    };

    public static Result run(TrnxRecord[] trnxFile, CardXrefRecord[] xrefFile,
                             CustomerRecord[] custFile, AccountRecord[] acctFile) {
        Result res = new Result();

        int nT = trnxFile == null ? 0 : trnxFile.length;
        String[] trnxTexts = new String[nT];
        for (int i = 0; i < nT; i++) {
            trnxTexts[i] = trnxText(trnxFile[i]);
        }
        int nX = xrefFile == null ? 0 : xrefFile.length;
        String[] xrefTexts = new String[nX];
        for (int i = 0; i < nX; i++) {
            xrefTexts[i] = xrefText(xrefFile[i]);
        }
        int nC = custFile == null ? 0 : custFile.length;
        String[] custKeys = new String[nC];
        String[] custTexts = new String[nC];
        for (int i = 0; i < nC; i++) {
            custTexts[i] = custText(custFile[i]);
            custKeys[i] = custTexts[i].substring(0, 9);
        }
        int nA = acctFile == null ? 0 : acctFile.length;
        String[] acctTexts = new String[nA];
        for (int i = 0; i < nA; i++) {
            acctTexts[i] = acctText(acctFile[i]);
        }

        // table memory: slots per card (card num + 10 tran entries), lazily filled
        String[] slots = new String[CARD_MAX * 11];
        long[] trct = new long[CARD_MAX];

        // 8100-TRNXFILE-OPEN
        int[] trnxSt = new int[2];
        String rc;
        String fldt = spaces(1000);
        rc = seqRead(trnxTexts, trnxSt);
        if (rc.equals("00")) {
            fldt = fix(trnxTexts[trnxSt[0] - 1], 1000);
        }
        if (!(rc.equals("00") || rc.equals("04"))) {
            return abend(res, "ERROR READING TRNXFILE", rc);
        }
        String trnxRecord = fldt.substring(0, 350);
        String saveCard = trnxRecord.substring(0, 16);
        long crCnt = 1;
        long trCnt = 0;

        // 8500-READTRNX-READ
        while (true) {
            String tCard = trnxRecord.substring(0, 16);
            String tId = trnxRecord.substring(16, 32);
            String tRest = trnxRecord.substring(32, 350);
            if (saveCard.equals(tCard)) {
                trCnt = (trCnt + 1) % 10000;
            } else {
                setTrct(trct, crCnt, trCnt);
                crCnt = (crCnt + 1) % 10000;
                trCnt = 1;
            }
            memWrite(slots, cardOff(crCnt), tCard);
            memWrite(slots, tranOff(crCnt, trCnt), tId);
            memWrite(slots, tranOff(crCnt, trCnt) + 16, tRest);
            saveCard = tCard;

            rc = seqRead(trnxTexts, trnxSt);
            if (rc.equals("00")) {
                fldt = fix(trnxTexts[trnxSt[0] - 1], 1000);
                trnxRecord = fldt.substring(0, 350);
            } else if (rc.equals("10")) {
                break;
            } else {
                return abend(res, "ERROR READING TRNXFILE", rc);
            }
        }
        // 8599-EXIT
        setTrct(trct, crCnt, trCnt);

        int[] xrefSt = new int[2];

        // 1000-MAINLINE
        boolean endOfFile = false;
        while (!endOfFile) {
            fldt = spaces(1000);
            rc = seqRead(xrefTexts, xrefSt);
            if (rc.equals("00")) {
                fldt = fix(xrefTexts[xrefSt[0] - 1], 1000);
            } else if (rc.equals("10")) {
                endOfFile = true;
            } else {
                return abend(res, "ERROR READING XREFFILE", rc);
            }
            if (endOfFile) {
                break;
            }
            String xrefCardNum = fldt.substring(0, 16);
            String xrefCustId = fldt.substring(16, 25);
            String xrefAcctId = fldt.substring(25, 36);

            // 2000-CUSTFILE-GET
            String custRec = null;
            for (int i = 0; i < nC; i++) {
                if (custKeys[i].equals(xrefCustId)) {
                    custRec = custTexts[i];
                    break;
                }
            }
            if (custRec == null) {
                return abend(res, "ERROR READING CUSTFILE", "23");
            }

            // 3000-ACCTFILE-GET
            String acctRec = null;
            for (int i = 0; i < nA; i++) {
                if (acctTexts[i].substring(0, 11).equals(xrefAcctId)) {
                    acctRec = acctTexts[i];
                    break;
                }
            }
            if (acctRec == null) {
                return abend(res, "ERROR READING ACCTFILE", "23");
            }

            // 5000-CREATE-STATEMENT
            createStatement(res, custRec, acctRec);

            // 4000-TRNXFILE-GET
            long total = 0;
            long crJmp = 1;
            while (true) {
                if (crJmp > crCnt) {
                    break;
                }
                String cn = memRead(slots, cardOff(crJmp), 16);
                if (ebcCompare(cn, xrefCardNum) > 0) {
                    break;
                }
                if (xrefCardNum.equals(cn)) {
                    long cnt = getTrct(trct, crJmp);
                    for (long trJmp = 1; trJmp <= cnt; trJmp++) {
                        String tid = memRead(slots, tranOff(crJmp, trJmp), 16);
                        String trest = memRead(slots, tranOff(crJmp, trJmp) + 16, 318);
                        long amt = decodeZoned(trest.substring(116, 127));
                        writeTrans(res, tid, trest, amt);
                        total = trunc11(total + amt);
                    }
                }
                crJmp++;
            }
            String stTotal = fmtZ(total);
            stmt(res, repeat('-', 80));
            stmt(res, "Total EXP:" + spaces(56) + "$" + stTotal);
            stmt(res, repeat('*', 32) + "END OF STATEMENT" + repeat('*', 32));

            html(res, LTRS);
            html(res, L10);
            html(res, L75);
            html(res, LTDE);
            html(res, LTRE);
            html(res, L78);
            html(res, L79);
            html(res, L80);
        }

        return res;
    }

    private static String trnxText(TrnxRecord r) {
        if (r == null) {
            return spaces(350);
        }
        return fix(r.trnxCardNum, 16) + fix(r.trnxId, 16) + fix(r.trnxTypeCd, 2) + zu(r.trnxCatCd, 4)
                + fix(r.trnxSource, 10) + fix(r.trnxDesc, 100) + zs(r.trnxAmt, 11) + zu(r.trnxMerchantId, 9)
                + fix(r.trnxMerchantName, 50) + fix(r.trnxMerchantCity, 50) + fix(r.trnxMerchantZip, 10)
                + fix(r.trnxOrigTs, 26) + fix(r.trnxProcTs, 26) + fix(r.filler1, 20);
    }

    private static String xrefText(CardXrefRecord r) {
        if (r == null) {
            return spaces(50);
        }
        return fix(r.xrefCardNum, 16) + zu(r.xrefCustId, 9) + zu(r.xrefAcctId, 11) + fix(r.filler1, 14);
    }

    private static String custText(CustomerRecord r) {
        if (r == null) {
            return spaces(500);
        }
        return zu(r.custId, 9) + fix(r.custFirstName, 25) + fix(r.custMiddleName, 25) + fix(r.custLastName, 25)
                + fix(r.custAddrLine1, 50) + fix(r.custAddrLine2, 50) + fix(r.custAddrLine3, 50)
                + fix(r.custAddrStateCd, 2) + fix(r.custAddrCountryCd, 3) + fix(r.custAddrZip, 10)
                + fix(r.custPhoneNum1, 15) + fix(r.custPhoneNum2, 15) + zu(r.custSsn, 9)
                + fix(r.custGovtIssuedId, 20) + fix(r.custDobYyyymmdd, 10) + fix(r.custEftAccountId, 10)
                + fix(r.custPriCardHolderInd, 1) + zu(r.custFicoCreditScore, 3) + fix(r.filler1, 168);
    }

    private static String acctText(AccountRecord r) {
        if (r == null) {
            return spaces(300);
        }
        return zu(r.acctId, 11) + fix(r.acctActiveStatus, 1) + zs(r.acctCurrBal, 12) + zs(r.acctCreditLimit, 12)
                + zs(r.acctCashCreditLimit, 12) + fix(r.acctOpenDate, 10) + fix(r.acctExpiraionDate, 10)
                + fix(r.acctReissueDate, 10) + zs(r.acctCurrCycCredit, 12) + zs(r.acctCurrCycDebit, 12)
                + fix(r.acctAddrZip, 10) + fix(r.acctGroupId, 10) + fix(r.filler1, 178);
    }

    private static void createStatement(Result res, String custRec, String acctRec) {
        String custFirst = custRec.substring(9, 34);
        String custMiddle = custRec.substring(34, 59);
        String custLast = custRec.substring(59, 84);
        String addr1 = custRec.substring(84, 134);
        String addr2 = custRec.substring(134, 184);
        String addr3 = custRec.substring(184, 234);
        String state = custRec.substring(234, 236);
        String country = custRec.substring(236, 239);
        String zip = custRec.substring(239, 249);
        String fico = custRec.substring(329, 332);

        String acctId = acctRec.substring(0, 11);
        long currBal = decodeZoned(acctRec.substring(12, 24));

        stmt(res, repeat('*', 31) + "START OF STATEMENT" + repeat('*', 31));

        // 5100-WRITE-HTML-HEADER
        html(res, L01);
        html(res, L02);
        html(res, L03);
        html(res, L04);
        html(res, L05);
        html(res, L06);
        html(res, L07);
        html(res, L08);
        html(res, LTRS);
        html(res, L10);
        html(res, "<h3>Statement for Account Number: " + fix(acctId, 20) + "</h3>");
        html(res, LTDE);
        html(res, LTRE);
        html(res, LTRS);
        html(res, L15);
        html(res, L16);
        html(res, L17);
        html(res, L18);
        html(res, LTDE);
        html(res, LTRE);
        html(res, LTRS);
        html(res, L22_35);

        StringBuilder nm = new StringBuilder();
        app(nm, 75, custFirst, " ");
        app(nm, 75, " ", null);
        app(nm, 75, custMiddle, " ");
        app(nm, 75, " ", null);
        app(nm, 75, custLast, " ");
        app(nm, 75, " ", null);
        String stName = fix(nm.toString(), 75);
        String stAdd1 = addr1;
        String stAdd2 = addr2;
        StringBuilder a3 = new StringBuilder();
        app(a3, 80, addr3, " ");
        app(a3, 80, " ", null);
        app(a3, 80, state, " ");
        app(a3, 80, " ", null);
        app(a3, 80, country, " ");
        app(a3, 80, " ", null);
        app(a3, 80, zip, " ");
        app(a3, 80, " ", null);
        String stAdd3 = fix(a3.toString(), 80);

        String stAcctId = fix(acctId, 20);
        String stCurrBal = fmtCurrBal(currBal);
        String stFico = fix(fico, 20);

        // 5200-WRITE-HTML-NMADBS
        String l23Name = stName.substring(0, 50);
        html(res, para("<p style=\"font-size:16px\">", l23Name));
        html(res, para("<p>", stAdd1));
        html(res, para("<p>", stAdd2));
        html(res, para("<p>", stAdd3));
        html(res, LTDE);
        html(res, LTRE);
        html(res, LTRS);
        html(res, L30_42);
        html(res, L31);
        html(res, LTDE);
        html(res, LTRE);
        html(res, LTRS);
        html(res, L22_35);
        html(res, star("<p>Account ID         : ", stAcctId));
        html(res, star("<p>Current Balance    : ", stCurrBal));
        html(res, star("<p>FICO Score         : ", stFico));
        html(res, LTDE);
        html(res, LTRE);
        html(res, LTRS);
        html(res, L30_42);
        html(res, L43);
        html(res, LTDE);
        html(res, LTRE);
        html(res, LTRS);
        html(res, L47);
        html(res, L48);
        html(res, LTDE);
        html(res, L50);
        html(res, L51);
        html(res, LTDE);
        html(res, L53);
        html(res, L54);
        html(res, LTDE);
        html(res, LTRE);

        String dashes = repeat('-', 80);
        stmt(res, stName + spaces(5));
        stmt(res, stAdd1 + spaces(30));
        stmt(res, stAdd2 + spaces(30));
        stmt(res, stAdd3);
        stmt(res, dashes);
        stmt(res, spaces(33) + "Basic Details " + spaces(33));
        stmt(res, dashes);
        stmt(res, "Account ID         :" + stAcctId + spaces(40));
        stmt(res, "Current Balance    :" + stCurrBal + spaces(47));
        stmt(res, "FICO Score         :" + stFico + spaces(40));
        stmt(res, dashes);
        stmt(res, spaces(30) + "TRANSACTION SUMMARY " + spaces(30));
        stmt(res, dashes);
        stmt(res, "Tran ID         " + fix("Tran Details    ", 51) + "  Tran Amount");
        stmt(res, dashes);
    }

    private static void writeTrans(Result res, String tid, String trest, long amt) {
        String stTranid = tid;
        String stTrandt = trest.substring(16, 65);
        String stTranamt = fmtZ(amt);
        stmt(res, stTranid + " " + stTrandt + "$" + stTranamt);

        html(res, LTRS);
        html(res, L58);
        html(res, star("<p>", stTranid));
        html(res, LTDE);
        html(res, L61);
        html(res, star("<p>", stTrandt));
        html(res, LTDE);
        html(res, L64);
        html(res, star("<p>", stTranamt));
        html(res, LTDE);
        html(res, LTRE);
    }

    private static String para(String prefix, String field) {
        StringBuilder b = new StringBuilder();
        app(b, 100, prefix, "*");
        app(b, 100, field, "  ");
        app(b, 100, "  ", null);
        app(b, 100, "</p>", "*");
        return fix(b.toString(), 100);
    }

    private static String star(String prefix, String field) {
        StringBuilder b = new StringBuilder();
        app(b, 100, prefix, "*");
        app(b, 100, field, "*");
        app(b, 100, "</p>", "*");
        return fix(b.toString(), 100);
    }

    private static void app(StringBuilder dst, int cap, String src, String delim) {
        String s = src;
        if (delim != null) {
            int idx = s.indexOf(delim);
            if (idx >= 0) {
                s = s.substring(0, idx);
            }
        }
        int room = cap - dst.length();
        if (room <= 0) {
            return;
        }
        if (s.length() > room) {
            s = s.substring(0, room);
        }
        dst.append(s);
    }

    private static Result abend(Result res, String msg, String rc) {
        res.displays.add(msg);
        res.displays.add("RETURN CODE: " + rc);
        res.displays.add("ABENDING PROGRAM");
        res.abended = true;
        return res;
    }

    private static String seqRead(String[] texts, int[] st) {
        if (st[1] != 0) {
            return "46";
        }
        if (st[0] < texts.length) {
            st[0]++;
            return "00";
        }
        st[1] = 1;
        return "10";
    }

    private static void stmt(Result res, String s) {
        res.stmtFileWrites.add(fix(s, 80));
    }

    private static void html(Result res, String s) {
        res.htmlFileWrites.add(fix(s, 100));
    }

    private static long cardOff(long cr) {
        return (cr - 1) * CARD_SZ;
    }

    private static long tranOff(long cr, long tr) {
        return (cr - 1) * CARD_SZ + 16 + (tr - 1) * TRAN_SZ;
    }

    // slot geometry
    private static int slotIndex(long off) {
        int c = (int) (off / CARD_SZ);
        int w = (int) (off % CARD_SZ);
        int k = w < 16 ? 0 : 1 + (w - 16) / TRAN_SZ;
        return c * 11 + k;
    }

    private static long slotStart(int idx) {
        int c = idx / 11;
        int k = idx % 11;
        long base = (long) c * CARD_SZ;
        if (k == 0) {
            return base;
        }
        return base + 16 + (long) (k - 1) * TRAN_SZ;
    }

    private static int slotLen(int idx) {
        return (idx % 11) == 0 ? 16 : TRAN_SZ;
    }

    private static void memWrite(String[] slots, long off, String s) {
        int pos = 0;
        int n = s.length();
        while (pos < n) {
            long o = off + pos;
            if (o < 0) {
                pos = (int) (-off);
                continue;
            }
            if (o >= MEM_SZ) {
                break;
            }
            int idx = slotIndex(o);
            int len = slotLen(idx);
            int within = (int) (o - slotStart(idx));
            int take = len - within;
            if (take > n - pos) {
                take = n - pos;
            }
            String cur = slots[idx];
            if (cur == null) {
                cur = spaces(len);
            }
            slots[idx] = cur.substring(0, within) + s.substring(pos, pos + take) + cur.substring(within + take);
            pos += take;
        }
    }

    private static String memRead(String[] slots, long off, int n) {
        StringBuilder sb = new StringBuilder();
        int pos = 0;
        while (pos < n) {
            long o = off + pos;
            if (o < 0) {
                int skip = (int) (-o);
                if (skip > n - pos) {
                    skip = n - pos;
                }
                sb.append(spaces(skip));
                pos += skip;
                continue;
            }
            if (o >= MEM_SZ) {
                sb.append(spaces(n - pos));
                break;
            }
            int idx = slotIndex(o);
            int len = slotLen(idx);
            int within = (int) (o - slotStart(idx));
            int take = len - within;
            if (take > n - pos) {
                take = n - pos;
            }
            String cur = slots[idx];
            if (cur == null) {
                sb.append(spaces(take));
            } else {
                sb.append(cur.substring(within, within + take));
            }
            pos += take;
        }
        return sb.toString();
    }

    private static void setTrct(long[] trct, long cr, long v) {
        if (cr >= 1 && cr <= CARD_MAX) {
            trct[(int) (cr - 1)] = v;
        }
    }

    private static long getTrct(long[] trct, long cr) {
        if (cr >= 1 && cr <= CARD_MAX) {
            return trct[(int) (cr - 1)];
        }
        return 0;
    }

    private static int ebc(char c) {
        for (int i = 0; i < 256; i++) {
            if (CP037[i] == c) {
                return i;
            }
        }
        return 256 + c;
    }

    private static int ebcCompare(String a, String b) {
        if (a.equals(b)) {
            return 0;
        }
        int n = a.length() > b.length() ? a.length() : b.length();
        for (int i = 0; i < n; i++) {
            char ca = i < a.length() ? a.charAt(i) : ' ';
            char cb = i < b.length() ? b.charAt(i) : ' ';
            if (ca != cb) {
                int wa = ebc(ca);
                int wb = ebc(cb);
                if (wa != wb) {
                    return wa < wb ? -1 : 1;
                }
            }
        }
        return 0;
    }

    private static long decodeZoned(String s) {
        long v = 0;
        boolean neg = false;
        int n = s.length();
        for (int i = 0; i < n; i++) {
            char c = s.charAt(i);
            int d;
            if (c >= '0' && c <= '9') {
                d = c - '0';
            } else if (i == n - 1) {
                if (c == '{') {
                    d = 0;
                } else if (c >= 'A' && c <= 'I') {
                    d = c - 'A' + 1;
                } else if (c == '}') {
                    d = 0;
                    neg = true;
                } else if (c >= 'J' && c <= 'R') {
                    d = c - 'J' + 1;
                    neg = true;
                } else if (c >= 'p' && c <= 'y') {
                    d = c - 'p';
                    neg = true;
                } else {
                    d = (c & 0x0F) % 10;
                }
            } else {
                d = (c & 0x0F) % 10;
            }
            v = v * 10 + d;
        }
        return neg ? -v : v;
    }

    private static long pow10(int n) {
        long p = 1;
        for (int i = 0; i < n; i++) {
            p = p * 10;
        }
        return p;
    }

    private static String zu(long v, int n) {
        long a = v < 0 ? -v : v;
        if (n < 19) {
            a = a % pow10(n);
        }
        return zeroPad(a, n);
    }

    private static String zs(long v, int n) {
        boolean neg = v < 0;
        long a = neg ? -v : v;
        if (n < 19) {
            a = a % pow10(n);
        }
        String z = zeroPad(a, n);
        int d = z.charAt(n - 1) - '0';
        char last;
        if (neg) {
            last = d == 0 ? '}' : (char) ('J' + d - 1);
        } else {
            last = d == 0 ? '{' : (char) ('A' + d - 1);
        }
        return z.substring(0, n - 1) + last;
    }

    private static long trunc11(long v) {
        boolean neg = v < 0;
        long a = neg ? -v : v;
        a = a % 100000000000L;
        return neg ? -a : a;
    }

    private static String fmtCurrBal(long v) {
        boolean neg = v < 0;
        long a = neg ? -v : v;
        a = a % 100000000000L;
        return zeroPad(a / 100, 9) + "." + zeroPad(a % 100, 2) + (neg ? "-" : " ");
    }

    private static String fmtZ(long v) {
        boolean neg = v < 0;
        long a = neg ? -v : v;
        a = a % 100000000000L;
        String ip = zeroPad(a / 100, 9);
        int k = 0;
        while (k < 9 && ip.charAt(k) == '0') {
            k++;
        }
        return spaces(k) + ip.substring(k) + "." + zeroPad(a % 100, 2) + (neg ? "-" : " ");
    }

    private static String zeroPad(long v, int n) {
        char[] c = new char[n];
        long x = v;
        for (int i = n - 1; i >= 0; i--) {
            c[i] = (char) ('0' + (x % 10));
            x = x / 10;
        }
        return new String(c);
    }

    private static String repeat(char ch, int n) {
        if (n <= 0) {
            return "";
        }
        String s = String.valueOf(ch);
        while (s.length() < n) {
            s = s + s;
        }
        return s.substring(0, n);
    }

    private static String spaces(int n) {
        return repeat(' ', n);
    }

    private static String fix(String s, int n) {
        String t = s == null ? "" : s;
        int len = t.length();
        if (len == n) {
            return t;
        }
        if (len > n) {
            return t.substring(0, n);
        }
        return t + spaces(n - len);
    }
}