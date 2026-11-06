      * G-initindex (GnuCOBOL deviation): INITIALIZE and index data
      * items. IBM excludes "Any identifiers that are not valid
      * receiving operands of a MOVE statement" (an index data item is
      * not one), so X1, K1 and X3 keep 5 and X1 keeps 6 under
      * REPLACING. GnuCOBOL 3.2 (-std=ibm) sets them to 0, and REPLACING
      * NUMERIC BY 11 sets X1 to 11:
      *   G1    00 X1=0000+
      *   G2 K1=0000+
      *   G3   X3=0000+
      *   G1R aa 11 X1=0011+
      *   X1-DIRECT 0000+
      * In the model INITIALIZE G1, G2, G3 and G1 REPLACING run and
      * leave the index items alone; INITIALIZE X1 is unsupported.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. IX2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05  A1 PIC X(2) VALUE "zz".
           05  X1 USAGE INDEX.
           05  N1 PIC 99 VALUE 77.
       01  G2 USAGE INDEX.
           05  K1.
           05  K2.
       01  G3.
           05  E3 OCCURS 2.
               10  B3 PIC X VALUE "q".
               10  X3 USAGE INDEX.
       01  TA.
           05  TAE PIC XX OCCURS 9 INDEXED BY IA.
       01  N PIC S9(4) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           SET IA TO 5.
           SET X1 TO IA. SET K1 TO IA. SET K2 TO IA.
           SET X3 (1) TO IA. SET X3 (2) TO IA.
           INITIALIZE G1.
           SET IA TO X1. SET N TO IA.
           DISPLAY "G1 " A1 " " N1 " X1=" N.
           INITIALIZE G2.
           SET IA TO K1. SET N TO IA.
           DISPLAY "G2 K1=" N.
           INITIALIZE G3.
           SET IA TO X3 (2). SET N TO IA.
           DISPLAY "G3 " B3 (1) " X3=" N.
           SET IA TO 6.
           SET X1 TO IA.
           INITIALIZE G1 REPLACING ALPHANUMERIC BY "aa" NUMERIC BY 11.
           SET IA TO X1. SET N TO IA.
           DISPLAY "G1R " A1 " " N1 " X1=" N.
           SET IA TO 7.
           SET X1 TO IA.
           INITIALIZE X1.
           SET IA TO X1. SET N TO IA.
           DISPLAY "X1-DIRECT " N.
           STOP RUN.
