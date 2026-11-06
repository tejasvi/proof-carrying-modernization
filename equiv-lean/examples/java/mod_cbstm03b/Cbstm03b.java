public final class Cbstm03b {

    public static final class FdTrnxfileRec {
        public String fdTrnxCard;
        public String fdTrnxId;
        public String fdAcctData;
        public FdTrnxfileRec(String fdTrnxCard, String fdTrnxId, String fdAcctData) {
            this.fdTrnxCard = fdTrnxCard;
            this.fdTrnxId = fdTrnxId;
            this.fdAcctData = fdAcctData;
        }
    }

    public static final class FdXreffileRec {
        public String fdXrefCardNum;
        public String fdXrefData;
        public FdXreffileRec(String fdXrefCardNum, String fdXrefData) {
            this.fdXrefCardNum = fdXrefCardNum;
            this.fdXrefData = fdXrefData;
        }
    }

    public static final class FdCustfileRec {
        public String fdCustId;
        public String fdCustData;
        public FdCustfileRec(String fdCustId, String fdCustData) {
            this.fdCustId = fdCustId;
            this.fdCustData = fdCustData;
        }
    }

    public static final class FdAcctfileRec {
        public long fdAcctId;
        public String fdAcctData;
        public FdAcctfileRec(long fdAcctId, String fdAcctData) {
            this.fdAcctId = fdAcctId;
            this.fdAcctData = fdAcctData;
        }
    }

    public static final class LkM03bArea {
        public String lkM03bDd;
        public String lkM03bOper;
        public String lkM03bRc;
        public String lkM03bKey;
        public long lkM03bKeyLn;
        public String lkM03bFldt;
        public LkM03bArea(String lkM03bDd, String lkM03bOper, String lkM03bRc, String lkM03bKey,
                          long lkM03bKeyLn, String lkM03bFldt) {
            this.lkM03bDd = lkM03bDd;
            this.lkM03bOper = lkM03bOper;
            this.lkM03bRc = lkM03bRc;
            this.lkM03bKey = lkM03bKey;
            this.lkM03bKeyLn = lkM03bKeyLn;
            this.lkM03bFldt = lkM03bFldt;
        }
    }

    public static final class TrnxFile {
        public boolean open;
        public FdTrnxfileRec[] recs;
        public int pos;
        public boolean eof;
        public TrnxFile(boolean open, FdTrnxfileRec[] recs, int pos, boolean eof) {
            this.open = open;
            this.recs = recs;
            this.pos = pos;
            this.eof = eof;
        }
    }

    public static final class XrefFile {
        public boolean open;
        public FdXreffileRec[] recs;
        public int pos;
        public boolean eof;
        public XrefFile(boolean open, FdXreffileRec[] recs, int pos, boolean eof) {
            this.open = open;
            this.recs = recs;
            this.pos = pos;
            this.eof = eof;
        }
    }

    public static final class CustFile {
        public boolean open;
        public FdCustfileRec[] recs;
        public int pos;
        public boolean eof;
        public CustFile(boolean open, FdCustfileRec[] recs, int pos, boolean eof) {
            this.open = open;
            this.recs = recs;
            this.pos = pos;
            this.eof = eof;
        }
    }

    public static final class AcctFile {
        public boolean open;
        public FdAcctfileRec[] recs;
        public int pos;
        public boolean eof;
        public AcctFile(boolean open, FdAcctfileRec[] recs, int pos, boolean eof) {
            this.open = open;
            this.recs = recs;
            this.pos = pos;
            this.eof = eof;
        }
    }

    public static final class State {
        public TrnxFile trnxFile;
        public XrefFile xrefFile;
        public CustFile custFile;
        public AcctFile acctFile;
        public FdTrnxfileRec fdTrnxfileRec;
        public FdXreffileRec fdXreffileRec;
        public FdCustfileRec fdCustfileRec;
        public FdAcctfileRec fdAcctfileRec;
        public String trnxfileStatus;
        public String xreffileStatus;
        public String custfileStatus;
        public String acctfileStatus;
        public State(TrnxFile trnxFile, XrefFile xrefFile, CustFile custFile, AcctFile acctFile,
                     FdTrnxfileRec fdTrnxfileRec, FdXreffileRec fdXreffileRec,
                     FdCustfileRec fdCustfileRec, FdAcctfileRec fdAcctfileRec,
                     String trnxfileStatus, String xreffileStatus,
                     String custfileStatus, String acctfileStatus) {
            this.trnxFile = trnxFile;
            this.xrefFile = xrefFile;
            this.custFile = custFile;
            this.acctFile = acctFile;
            this.fdTrnxfileRec = fdTrnxfileRec;
            this.fdXreffileRec = fdXreffileRec;
            this.fdCustfileRec = fdCustfileRec;
            this.fdAcctfileRec = fdAcctfileRec;
            this.trnxfileStatus = trnxfileStatus;
            this.xreffileStatus = xreffileStatus;
            this.custfileStatus = custfileStatus;
            this.acctfileStatus = acctfileStatus;
        }
    }

    public static void call(Integer[] openErrors, State st, LkM03bArea area) {
        String dd = area.lkM03bDd;
        String op = area.lkM03bOper;
        if ("TRNXFILE".equals(dd)) {
            trnxProc(openErrors, st, area, op);
        } else if ("XREFFILE".equals(dd)) {
            xrefProc(openErrors, st, area, op);
        } else if ("CUSTFILE".equals(dd)) {
            custProc(openErrors, st, area, op);
        } else if ("ACCTFILE".equals(dd)) {
            acctProc(openErrors, st, area, op);
        }
        // WHEN OTHER: GO TO 9999-GOBACK, nothing changes
    }

    // ---------------- TRNXFILE ----------------
    private static void trnxProc(Integer[] openErrors, State st, LkM03bArea area, String op) {
        TrnxFile f = st.trnxFile;
        if ("O".equals(op)) {
            String s;
            if (f.open) {
                s = "41";
            } else if (openErrors != null && openErrors.length > 0 && openErrors[0] != null) {
                s = status2(openErrors[0].intValue());
            } else {
                s = "00";
                f.open = true;
                f.pos = 0;
                f.eof = false;
            }
            st.trnxfileStatus = s;
        } else if ("R".equals(op)) {
            String s;
            if (!f.open) {
                s = "47";
            } else if (f.eof) {
                s = "46";
            } else if (f.recs == null || f.pos >= f.recs.length) {
                s = "10";
                f.eof = true;
            } else {
                s = "00";
                FdTrnxfileRec r = f.recs[f.pos];
                f.pos += 1;
                st.fdTrnxfileRec = new FdTrnxfileRec(r.fdTrnxCard, r.fdTrnxId, r.fdAcctData);
                String img = fit(r.fdTrnxCard, 16) + fit(r.fdTrnxId, 16) + fit(r.fdAcctData, 318);
                area.lkM03bFldt = fit(img, 1000);
            }
            st.trnxfileStatus = s;
        } else if ("C".equals(op)) {
            String s;
            if (!f.open) {
                s = "42";
            } else {
                s = "00";
                f.open = false;
            }
            st.trnxfileStatus = s;
        }
        area.lkM03bRc = st.trnxfileStatus;
    }

    // ---------------- XREFFILE ----------------
    private static void xrefProc(Integer[] openErrors, State st, LkM03bArea area, String op) {
        XrefFile f = st.xrefFile;
        if ("O".equals(op)) {
            String s;
            if (f.open) {
                s = "41";
            } else if (openErrors != null && openErrors.length > 1 && openErrors[1] != null) {
                s = status2(openErrors[1].intValue());
            } else {
                s = "00";
                f.open = true;
                f.pos = 0;
                f.eof = false;
            }
            st.xreffileStatus = s;
        } else if ("R".equals(op)) {
            String s;
            if (!f.open) {
                s = "47";
            } else if (f.eof) {
                s = "46";
            } else if (f.recs == null || f.pos >= f.recs.length) {
                s = "10";
                f.eof = true;
            } else {
                s = "00";
                FdXreffileRec r = f.recs[f.pos];
                f.pos += 1;
                st.fdXreffileRec = new FdXreffileRec(r.fdXrefCardNum, r.fdXrefData);
                String img = fit(r.fdXrefCardNum, 16) + fit(r.fdXrefData, 34);
                area.lkM03bFldt = fit(img, 1000);
            }
            st.xreffileStatus = s;
        } else if ("C".equals(op)) {
            String s;
            if (!f.open) {
                s = "42";
            } else {
                s = "00";
                f.open = false;
            }
            st.xreffileStatus = s;
        }
        area.lkM03bRc = st.xreffileStatus;
    }

    // ---------------- CUSTFILE ----------------
    private static void custProc(Integer[] openErrors, State st, LkM03bArea area, String op) {
        CustFile f = st.custFile;
        if ("O".equals(op)) {
            String s;
            if (f.open) {
                s = "41";
            } else if (openErrors != null && openErrors.length > 2 && openErrors[2] != null) {
                s = status2(openErrors[2].intValue());
            } else {
                s = "00";
                f.open = true;
                f.pos = 0;
                f.eof = false;
            }
            st.custfileStatus = s;
        } else if ("K".equals(op)) {
            String keyPart = keySub(area);
            if (st.fdCustfileRec == null) {
                st.fdCustfileRec = new FdCustfileRec(spaces(9), spaces(491));
            }
            st.fdCustfileRec.fdCustId = fit(keyPart, 9);
            String s;
            if (!f.open) {
                s = "47";
            } else {
                int found = -1;
                if (f.recs != null) {
                    for (int i = 0; i < f.recs.length; i++) {
                        if (f.recs[i] != null && st.fdCustfileRec.fdCustId.equals(f.recs[i].fdCustId)) {
                            found = i;
                            break;
                        }
                    }
                }
                if (found < 0) {
                    s = "23";
                } else {
                    s = "00";
                    f.pos = found + 1;
                    f.eof = false;
                    FdCustfileRec r = f.recs[found];
                    st.fdCustfileRec = new FdCustfileRec(r.fdCustId, r.fdCustData);
                    String img = fit(r.fdCustId, 9) + fit(r.fdCustData, 491);
                    area.lkM03bFldt = fit(img, 1000);
                }
            }
            st.custfileStatus = s;
        } else if ("C".equals(op)) {
            String s;
            if (!f.open) {
                s = "42";
            } else {
                s = "00";
                f.open = false;
            }
            st.custfileStatus = s;
        }
        area.lkM03bRc = st.custfileStatus;
    }

    // ---------------- ACCTFILE ----------------
    private static void acctProc(Integer[] openErrors, State st, LkM03bArea area, String op) {
        AcctFile f = st.acctFile;
        if ("O".equals(op)) {
            String s;
            if (f.open) {
                s = "41";
            } else if (openErrors != null && openErrors.length > 3 && openErrors[3] != null) {
                s = status2(openErrors[3].intValue());
            } else {
                s = "00";
                f.open = true;
                f.pos = 0;
                f.eof = false;
            }
            st.acctfileStatus = s;
        } else if ("K".equals(op)) {
            String keyPart = keySub(area);
            long v = 0L;
            for (int i = 0; i < keyPart.length(); i++) {
                char c = keyPart.charAt(i);
                int d = 0;
                if (c >= '0' && c <= '9') {
                    d = c - '0';
                }
                v = (v * 10L + d) % 100000000000L;
            }
            if (st.fdAcctfileRec == null) {
                st.fdAcctfileRec = new FdAcctfileRec(0L, spaces(289));
            }
            st.fdAcctfileRec.fdAcctId = v;
            String s;
            if (!f.open) {
                s = "47";
            } else {
                int found = -1;
                if (f.recs != null) {
                    for (int i = 0; i < f.recs.length; i++) {
                        if (f.recs[i] != null && f.recs[i].fdAcctId == st.fdAcctfileRec.fdAcctId) {
                            found = i;
                            break;
                        }
                    }
                }
                if (found < 0) {
                    s = "23";
                } else {
                    s = "00";
                    f.pos = found + 1;
                    f.eof = false;
                    FdAcctfileRec r = f.recs[found];
                    st.fdAcctfileRec = new FdAcctfileRec(r.fdAcctId, r.fdAcctData);
                    String img = zeroPad(r.fdAcctId, 11) + fit(r.fdAcctData, 289);
                    area.lkM03bFldt = fit(img, 1000);
                }
            }
            st.acctfileStatus = s;
        } else if ("C".equals(op)) {
            String s;
            if (!f.open) {
                s = "42";
            } else {
                s = "00";
                f.open = false;
            }
            st.acctfileStatus = s;
        }
        area.lkM03bRc = st.acctfileStatus;
    }

    // ---------------- helpers ----------------
    private static String keySub(LkM03bArea area) {
        String key = area.lkM03bKey == null ? "" : area.lkM03bKey;
        long kl = area.lkM03bKeyLn;
        int k;
        if (kl <= 0) {
            k = 0;
        } else if (kl > key.length()) {
            k = key.length();
        } else {
            k = (int) kl;
        }
        return key.substring(0, k);
    }

    private static String status2(int c) {
        int v = c % 100;
        if (v < 0) {
            v = -v;
        }
        StringBuilder sb = new StringBuilder();
        sb.append((char) ('0' + (v / 10)));
        sb.append((char) ('0' + (v % 10)));
        return sb.toString();
    }

    private static String fit(String s, int n) {
        if (s == null) {
            s = "";
        }
        if (s.length() == n) {
            return s;
        }
        if (s.length() > n) {
            return s.substring(0, n);
        }
        StringBuilder sb = new StringBuilder(n);
        sb.append(s);
        while (sb.length() < n) {
            sb.append(' ');
        }
        return sb.toString();
    }

    private static String spaces(int n) {
        StringBuilder sb = new StringBuilder(n);
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
            buf[i] = (char) ('0' + (int) (v % 10L));
            v = v / 10L;
        }
        return new String(buf);
    }
}