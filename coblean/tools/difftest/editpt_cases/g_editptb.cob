      * G-editptb (GnuCOBOL 3.2 departs from IBM): a B or , insertion
      * character right after the decimal point (or V), when the integer
      * part is a zero-suppression or floating string and zero, is
      * written as 0 by GnuCOBOL. IBM: suppression "stops at the
      * leftmost character ... That is the decimal point", so it is an
      * ordinary simple insertion character (B a space). / and 0 there
      * agree (B08 B09); with a nonzero integer part B agrees (B10).
      * IBM's result in each comment (the model's).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GEDITPTB.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E1 PIC ZZ.B99.
       01  E2 PIC $$.B99.
       01  E3 PIC **.B99.
       01  E4 PIC ZZVB99.
       01  E5 PIC ZZ.,99.
       01  E6 PIC ZZ,.B99.
       01  E7 PIC ZZ./99.
       01  E8 PIC ZZ.099.
       PROCEDURE DIVISION.
       P0.
      *    "  . 05" "  . 00" " $. 05" "**. 05" "   05" "  .,05"
           MOVE 0.05 TO E1 DISPLAY 'B01 [' E1 ']'
           MOVE 0 TO E1 DISPLAY 'B02 [' E1 ']'
           MOVE 0.05 TO E2 DISPLAY 'B03 [' E2 ']'
           MOVE 0.05 TO E3 DISPLAY 'B04 [' E3 ']'
           MOVE 0.05 TO E4 DISPLAY 'B05 [' E4 ']'
           MOVE 0.05 TO E5 DISPLAY 'B06 [' E5 ']'
      *    "   . 05"; agree: "  ./05" "  .005" " 1. 05"
           MOVE 0.05 TO E6 DISPLAY 'B07 [' E6 ']'
           MOVE 0.05 TO E7 DISPLAY 'B08 [' E7 ']'
           MOVE 0.05 TO E8 DISPLAY 'B09 [' E8 ']'
           MOVE 1.05 TO E1 DISPLAY 'B10 [' E1 ']'
           STOP RUN.
