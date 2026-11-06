      * G-floatcs (GnuCOBOL 3.2 departs from IBM): an arithmetic
      * statement (COMPUTE, ADD ... GIVING) storing into a numeric-
      * edited item whose floating currency string has an insertion
      * symbol right after its first symbol drops the leftmost digit
      * (H03 H04 H07); MOVE (H01 H02 H08), a floating + (H06) and an
      * insertion later in the string (H05) are right. IBM: the digit
      * positions are the floating symbols after the first one (3 in
      * $,$$$.9).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GFLTCS.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 N1 PIC S9(5)V99 VALUE 851.
       01 E1 PIC $,$$$.9.
       01 E2 PIC $$,$$9.9.
       01 E3 PIC +,+++.9.
       01 E4 PIC $B$$.99.
       PROCEDURE DIVISION.
           MOVE 851 TO E1 DISPLAY "H01 [" E1 "]|"
           MOVE N1 TO E1 DISPLAY "H02 [" E1 "]|"
           COMPUTE E1 = N1 + 0 DISPLAY "H03 [" E1 "]|"
           ADD 0 TO N1 GIVING E1 DISPLAY "H04 [" E1 "]|"
           COMPUTE E2 = N1 + 0 DISPLAY "H05 [" E2 "]|"
           COMPUTE E3 = N1 + 0 DISPLAY "H06 [" E3 "]|"
           MOVE 51 TO N1
           COMPUTE E4 = N1 + 0 DISPLAY "H07 [" E4 "]|"
           MOVE N1 TO E4 DISPLAY "H08 [" E4 "]|"
           STOP RUN.
