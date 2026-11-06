import java.util.ArrayList;
import java.util.List;

public final class Cbcus01c {

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
        public String custDobYyyyMmDd;
        public String custEftAccountId;
        public String custPriCardHolderInd;
        public long custFicoCreditScore;
        public String filler1;

        public CustomerRecord(long custId, String custFirstName, String custMiddleName,
                              String custLastName, String custAddrLine1, String custAddrLine2,
                              String custAddrLine3, String custAddrStateCd, String custAddrCountryCd,
                              String custAddrZip, String custPhoneNum1, String custPhoneNum2,
                              long custSsn, String custGovtIssuedId, String custDobYyyyMmDd,
                              String custEftAccountId, String custPriCardHolderInd,
                              long custFicoCreditScore, String filler1) {
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
            this.custDobYyyyMmDd = custDobYyyyMmDd;
            this.custEftAccountId = custEftAccountId;
            this.custPriCardHolderInd = custPriCardHolderInd;
            this.custFicoCreditScore = custFicoCreditScore;
            this.filler1 = filler1;
        }
    }

    public static final class Result {
        public List<String> displays = new ArrayList<String>();
        public boolean abended = false;
    }

    public static Result run(CustomerRecord[] custfileFile) {
        Result r = new Result();
        r.displays.add("START OF EXECUTION OF PROGRAM CBCUS01C");

        // 0000-CUSTFILE-OPEN: OPEN INPUT always succeeds ('00')
        String custfileStatus = "00";
        long applResult = 8;
        if (custfileStatus.equals("00")) {
            applResult = 0;
        } else {
            applResult = 12;
        }
        if (applResult != 0) {
            r.displays.add("ERROR OPENING CUSTFILE");
            displayIoStatus(r, custfileStatus);
            r.displays.add("ABENDING PROGRAM");
            r.abended = true;
            return r;
        }

        // CUSTOMER-RECORD initial storage (no VALUE clause)
        String customerRecord = fmtRecordInitial();
        int pos = 0;
        boolean eofReached = false;
        char endOfFile = 'N';

        while (endOfFile != 'Y') {
            if (endOfFile == 'N') {
                // 1000-CUSTFILE-GET-NEXT
                if (eofReached) {
                    custfileStatus = "46";
                } else if (custfileFile == null || pos >= custfileFile.length) {
                    custfileStatus = "10";
                    eofReached = true;
                } else {
                    customerRecord = fmtRecord(custfileFile[pos]);
                    pos++;
                    custfileStatus = "00";
                }
                if (custfileStatus.equals("00")) {
                    applResult = 0;
                    r.displays.add(customerRecord);
                } else if (custfileStatus.equals("10")) {
                    applResult = 16;
                } else {
                    applResult = 12;
                }
                if (applResult == 0) {
                    // continue
                } else if (applResult == 16) {
                    endOfFile = 'Y';
                } else {
                    r.displays.add("ERROR READING CUSTOMER FILE");
                    displayIoStatus(r, custfileStatus);
                    r.displays.add("ABENDING PROGRAM");
                    r.abended = true;
                    return r;
                }
                if (endOfFile == 'N') {
                    r.displays.add(customerRecord);
                }
            }
        }

        // 9000-CUSTFILE-CLOSE: CLOSE always succeeds ('00')
        custfileStatus = "00";
        applResult = 8;
        if (custfileStatus.equals("00")) {
            applResult = applResult - applResult;
        } else {
            applResult = 12;
        }
        if (applResult != 0) {
            r.displays.add("ERROR CLOSING CUSTOMER FILE");
            displayIoStatus(r, custfileStatus);
            r.displays.add("ABENDING PROGRAM");
            r.abended = true;
            return r;
        }

        r.displays.add("END OF EXECUTION OF PROGRAM CBCUS01C");
        return r;
    }

    private static void displayIoStatus(Result r, String status) {
        char s1 = status.charAt(0);
        char s2 = status.charAt(1);
        boolean numeric = (s1 >= '0' && s1 <= '9') && (s2 >= '0' && s2 <= '9');
        if (!numeric || s1 == '9') {
            int code = (int) s2;
            if (code > 255) {
                code = code & 0xFF;
            }
            String digits = fmtNum(code, 3);
            r.displays.add("FILE STATUS IS: NNNN" + s1 + digits);
        } else {
            r.displays.add("FILE STATUS IS: NNNN" + "00" + status);
        }
    }

    private static String fmtRecordInitial() {
        StringBuilder sb = new StringBuilder();
        sb.append(fmtNum(0, 9));
        sb.append(spaces(25 + 25 + 25 + 50 + 50 + 50 + 2 + 3 + 10 + 15 + 15));
        sb.append(fmtNum(0, 9));
        sb.append(spaces(20 + 10 + 10 + 1));
        sb.append(fmtNum(0, 3));
        sb.append(spaces(168));
        return sb.toString();
    }

    private static String fmtRecord(CustomerRecord c) {
        StringBuilder sb = new StringBuilder();
        sb.append(fmtNum(c.custId, 9));
        sb.append(fit(c.custFirstName, 25));
        sb.append(fit(c.custMiddleName, 25));
        sb.append(fit(c.custLastName, 25));
        sb.append(fit(c.custAddrLine1, 50));
        sb.append(fit(c.custAddrLine2, 50));
        sb.append(fit(c.custAddrLine3, 50));
        sb.append(fit(c.custAddrStateCd, 2));
        sb.append(fit(c.custAddrCountryCd, 3));
        sb.append(fit(c.custAddrZip, 10));
        sb.append(fit(c.custPhoneNum1, 15));
        sb.append(fit(c.custPhoneNum2, 15));
        sb.append(fmtNum(c.custSsn, 9));
        sb.append(fit(c.custGovtIssuedId, 20));
        sb.append(fit(c.custDobYyyyMmDd, 10));
        sb.append(fit(c.custEftAccountId, 10));
        sb.append(fit(c.custPriCardHolderInd, 1));
        sb.append(fmtNum(c.custFicoCreditScore, 3));
        sb.append(fit(c.filler1, 168));
        return sb.toString();
    }

    private static String fmtNum(long v, int n) {
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

    private static String fit(String s, int n) {
        if (s == null) {
            s = "";
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

    private static String spaces(int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            sb.append(' ');
        }
        return sb.toString();
    }
}