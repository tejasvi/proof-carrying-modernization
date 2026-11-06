       IDENTIFICATION DIVISION.
       PROGRAM-ID. VINTFN1.
      * dmax-fix stage D: integer intrinsic functions next to a division
      * where GnuCOBOL -std=ibm and IBM give the same values (the cases
      * where the function's places would change the quotient are in
      * g_intfn1.cob).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 A    PIC 99 VALUE 10.
       77 B    PIC 9 VALUE 3.
       77 D5   PIC 9V9(4) VALUE 1.2345.
       77 SN   PIC S9V99 VALUE -1.25.
       77 N0   PIC S9(5).
       77 N1   PIC S9(4)V9.
       77 EN0  PIC -(5)9.
       77 EN1  PIC -(4)9.9.
       PROCEDURE DIVISION.
      * INTEGER(1.2345) * (10 / 3) = 1 * 3 = 3
           COMPUTE N0 = FUNCTION INTEGER (D5) * (A / B).
           MOVE N0 TO EN0.
           DISPLAY 'F05 [' EN0 ']|'.
      * dmax 1: INTEGER-PART(1.2345) + 3.3 = 4.3
           COMPUTE N1 = FUNCTION INTEGER-PART (D5) + A / B.
           MOVE N1 TO EN1.
           DISPLAY 'F06 [' EN1 ']|'.
      * MOD(10, 3) + 10 / 3 = 1 + 3 = 4
           COMPUTE N0 = FUNCTION MOD (A, B) + A / B.
           MOVE N0 TO EN0.
           DISPLAY 'F07 [' EN0 ']|'.
      * negative arguments: INTEGER(-1.25) = -2, INTEGER-PART(-1.25) = -1
           COMPUTE N0 = FUNCTION INTEGER (SN).
           MOVE N0 TO EN0.
           DISPLAY 'F08 [' EN0 ']|'.
           COMPUTE N0 = FUNCTION INTEGER-PART (SN).
           MOVE N0 TO EN0.
           DISPLAY 'F09 [' EN0 ']|'.
           STOP RUN.
