      * Account master record (copybook)
       01  ACCT-REC.
           05  ACCT-ID          PIC X(8).
           05  ACCT-TYPE        PIC X.
           05  ACCT-BALANCE     PIC S9(11)V99 COMP-3.
           05  ACCT-BAL-RAW REDEFINES ACCT-BALANCE
                                PIC X(7).
           05  ACCT-RATE        PIC SV9(5)    COMP-3.
           05  ACCT-DAYS        PIC 9(3)      COMP.
