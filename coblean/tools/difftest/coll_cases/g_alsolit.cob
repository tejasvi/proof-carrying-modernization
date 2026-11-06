      * G-alsolit: GnuCOBOL 3.2 decides = and <> between two literals
      * by their bytes, ignoring a PROGRAM COLLATING SEQUENCE that puts
      * both characters in one position (ALSO); for < it uses the
      * sequence. IBM: "the characters D, N, and % are all considered
      * to be in the same position in the collating sequence", so "0" =
      * "9" is true. The model follows IBM: L01 L02 L03 differ.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GALSOL.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       OBJECT-COMPUTER. X
           PROGRAM COLLATING SEQUENCE IS SEQ1.
       SPECIAL-NAMES.
           ALPHABET SEQ1 IS "N" ALSO HIGH-VALUE ALSO LOW-VALUE "0" ALSO
              "9".
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 C1 PIC X VALUE "0".
       PROCEDURE DIVISION.
           IF "0" = "9" DISPLAY "L01 Y" ELSE DISPLAY "L01 N".
           IF "N" = X"FF" DISPLAY "L02 Y" ELSE DISPLAY "L02 N".
           IF "N" NOT = X"00" DISPLAY "L03 Y" ELSE DISPLAY "L03 N".
           IF "0" < "9" DISPLAY "L04 Y" ELSE DISPLAY "L04 N".
           IF "9" < "0" DISPLAY "L05 Y" ELSE DISPLAY "L05 N".
           IF C1 = "9" DISPLAY "L06 Y" ELSE DISPLAY "L06 N".
           STOP RUN.
