      * G-bwzv (GnuCOBOL 3.2 departs from IBM): BLANK WHEN ZERO on a
      * numeric item with V. IBM: the item becomes numeric-edited and V
      * is "Not counted in the size of the elementary item" (5 bytes
      * here); GnuCOBOL makes the item 6 bytes long (Z05 Z06).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GBWZV.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 B3 PIC 9(3)V99 BLANK WHEN ZERO.
       PROCEDURE DIVISION.
           MOVE 12.345 TO B3 DISPLAY "Z05 [" B3 "]|"
           MOVE 0.001 TO B3 DISPLAY "Z06 [" B3 "]|"
           STOP RUN.
