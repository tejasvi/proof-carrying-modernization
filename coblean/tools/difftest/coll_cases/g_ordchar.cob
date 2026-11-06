      * G-ordchar: under an ALPHABET of literals GnuCOBOL 3.2 computes
      * ORD and CHAR in the native order. IBM: ORD is "the ordinal
      * position of its argument in the collating sequence for the
      * program", CHAR the character at that position ("that of the
      * first literal specified for that character position"). The
      * model follows IBM (ORD("F") = 1, CHAR(3) = "N"): O and H lines
      * differ.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GORDCH.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       OBJECT-COMPUTER. X
           PROGRAM COLLATING SEQUENCE IS SEQ1.
       SPECIAL-NAMES.
           ALPHABET SEQ1 IS "F" "U" "N" ALSO HIGH-VALUE ALSO LOW-VALUE
              "Y".
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 C1 PIC X VALUE "U".
       01 N3 PIC 999.
       PROCEDURE DIVISION.
           COMPUTE N3 = FUNCTION ORD("F") DISPLAY "O1 " N3.
           COMPUTE N3 = FUNCTION ORD(C1) DISPLAY "O2 " N3.
           COMPUTE N3 = FUNCTION ORD("A") DISPLAY "O3 " N3.
           MOVE FUNCTION CHAR(1) TO C1 DISPLAY "H1 " C1 "|".
           MOVE FUNCTION CHAR(3) TO C1 DISPLAY "H2 " C1 "|".
           MOVE FUNCTION CHAR(66) TO C1 DISPLAY "H3 " C1 "|".
           STOP RUN.
