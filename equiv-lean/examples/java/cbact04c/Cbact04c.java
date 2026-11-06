import java.util.ArrayList;

/**
 * Java port of CardDemo's CBACT04C (monthly interest on category balances), for the COBOL → Java
 * proof against coblean's all-input theorem {@code cbact04c_all}.
 *
 * <p>The files of the COBOL program are arguments and results, as a data-access layer would
 * provide them: the category-balance records in file order (TCATBAL), the account and
 * disclosure-group records, looked up by key like the keyed READs (ACCTDAT, DISCGRP), and as
 * results the rewritten accounts in REWRITE order and the number of interest transactions
 * written (TRANSACT).  Amounts are in cents and rates in hundredths of a percent, as in the
 * {@code PIC S9(n)V99} fields; the truncation of an ADD or COMPUTE into a smaller field is
 * explicit ({@code S9(9)V99}: remainder modulo 10^11, {@code S9(10)V99}: modulo 10^12).
 *
 * <p>Like the COBOL program, the interest of the last account in the file is never posted: the
 * {@code ELSE PERFORM 1050-UPDATE-ACCOUNT} branch of the main loop is dead (CardDemo issue #64).
 */
public final class Cbact04c {
    /** TRAN-CAT-BAL-RECORD. */
    public static final class Cat {
        public final long acctId;
        public final String typeCd;
        public final int catCd;
        public final long bal;

        public Cat(long acctId, String typeCd, int catCd, long bal) {
            this.acctId = acctId;
            this.typeCd = typeCd;
            this.catCd = catCd;
            this.bal = bal;
        }
    }

    /** ACCOUNT-RECORD: the fields the program reads or changes. */
    public static final class Account {
        public final long id;
        public final long bal;
        public final long cycCredit;
        public final long cycDebit;
        public final String groupId;

        public Account(long id, long bal, long cycCredit, long cycDebit, String groupId) {
            this.id = id;
            this.bal = bal;
            this.cycCredit = cycCredit;
            this.cycDebit = cycDebit;
            this.groupId = groupId;
        }
    }

    /** DIS-GROUP-RECORD. */
    public static final class Disc {
        public final String groupId;
        public final String typeCd;
        public final int catCd;
        public final long rate;

        public Disc(String groupId, String typeCd, int catCd, long rate) {
            this.groupId = groupId;
            this.typeCd = typeCd;
            this.catCd = catCd;
            this.rate = rate;
        }
    }

    /** The REWRITEs, in order, and the number of transactions written. */
    public static final class Result {
        public final ArrayList<Account> rewrites;
        public final int transactions;

        public Result(ArrayList<Account> rewrites, int transactions) {
            this.rewrites = rewrites;
            this.transactions = transactions;
        }
    }

    /** 1100-GET-ACCT-DATA: the account record with this key. */
    static Account readAccount(Account[] accounts, long id) {
        for (int i = 0; i < accounts.length; i++) {
            if (accounts[i].id == id) {
                return accounts[i];
            }
        }
        return null;
    }

    /** 1200-GET-INTEREST-RATE, with 1200-A-GET-DEFAULT-INT-RATE when the key is not found. */
    static long readRate(Disc[] discs, String groupId, String typeCd, int catCd) {
        for (int i = 0; i < discs.length; i++) {
            Disc d = discs[i];
            if (d.groupId.equals(groupId) && d.typeCd.equals(typeCd) && d.catCd == catCd) {
                return d.rate;
            }
        }
        for (int i = 0; i < discs.length; i++) {
            Disc d = discs[i];
            if (d.groupId.equals("DEFAULT") && d.typeCd.equals(typeCd) && d.catCd == catCd) {
                return d.rate;
            }
        }
        throw new IllegalStateException("no disclosure group record");
    }

    /** 1050-UPDATE-ACCOUNT: post the interest, zero the cycle credit and debit. */
    static Account post(Account a, long totalInt) {
        return new Account(a.id, (a.bal + totalInt) % 1_000_000_000_000L, 0, 0, a.groupId);
    }

    /** The main loop of the PROCEDURE DIVISION. */
    public static Result run(Cat[] cats, Account[] accounts, Disc[] discs) {
        ArrayList<Account> rewrites = new ArrayList<>();
        int transactions = 0;
        boolean firstTime = true;
        long lastAcct = 0;
        long totalInt = 0;
        Account acct = null;
        for (int i = 0; i < cats.length; i++) {
            Cat c = cats[i];
            // WS-LAST-ACCT-NUM holds spaces until the first record: no account id equals it
            if (firstTime || c.acctId != lastAcct) {
                if (!firstTime) {
                    rewrites.add(post(acct, totalInt));
                } else {
                    firstTime = false;
                }
                totalInt = 0;
                lastAcct = c.acctId;
                acct = readAccount(accounts, c.acctId);
            }
            long rate = readRate(discs, acct.groupId, c.typeCd, c.catCd);
            if (rate != 0) {
                // 1300-COMPUTE-INTEREST and 1300-B-WRITE-TX
                long monthly = c.bal * rate / 120_000 % 100_000_000_000L;
                totalInt = (totalInt + monthly) % 100_000_000_000L;
                transactions++;
            }
        }
        return new Result(rewrites, transactions);
    }
}
