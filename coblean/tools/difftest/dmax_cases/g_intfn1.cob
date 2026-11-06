       IDENTIFICATION DIVISION.
       PROGRAM-ID. GINTFN1.
      * dmax-fix stage D: integer intrinsic functions contribute no
      * decimal places to dmax (IBM: "Integer intrinsic functions return
      * an integer; thus their outer-dmax is always zero"). GnuCOBOL
      * -std=ibm keeps more places for these quotients (G-osvsdiv: 34,
      * 34, 34.3, 34). Model: IBM.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 A    PIC 99 VALUE 10.
       77 B    PIC 9 VALUE 3.
       77 D5   PIC 9V9(4) VALUE 1.2345.
       77 N0   PIC S9(5).
       77 N1   PIC S9(4)V9.
       77 EN0  PIC -(5)9.
       77 EN1  PIC -(4)9.9.
       PROCEDURE DIVISION.
      * dmax 0: 10 / 3 = 3, * 10 = 30, + INTEGER(1.2345) = 31
           COMPUTE N0 = A / B * 10 + FUNCTION INTEGER (D5).
           MOVE N0 TO EN0.
           DISPLAY 'F01 [' EN0 ']|'.
      * INTEGER-PART, the same: 31
           COMPUTE N0 = A / B * 10 + FUNCTION INTEGER-PART (D5).
           MOVE N0 TO EN0.
           DISPLAY 'F02 [' EN0 ']|'.
      * dmax 1 (the receiver): 3.3 * 10 = 33.0, + 1 = 34.0
           COMPUTE N1 = A / B * 10 + FUNCTION INTEGER (D5).
           MOVE N1 TO EN1.
           DISPLAY 'F03 [' EN1 ']|'.
      * MOD of integers: dmax 0: 30 + MOD(10, 3) = 31
           COMPUTE N0 = A / B * 10 + FUNCTION MOD (A, B).
           MOVE N0 TO EN0.
           DISPLAY 'F04 [' EN0 ']|'.
           STOP RUN.
