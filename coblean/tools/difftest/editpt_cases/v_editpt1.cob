      * M-editpoint (fixed): a simple insertion character (B , 0 /)
      * right before the decimal point, after a zero-suppression or
      * floating insertion string with no 9, is part of the string
      * (IBM: "Any simple insertion symbols (B 0 / ,) within or to the
      * immediate right of the string ... are considered part of the
      * string"): with a zero integer part it is replaced, and a
      * floating symbol goes immediately left of the decimal point.
      * B and , here (GnuCOBOL agrees; for 0 and / see g_editins_pt).
      * Also the theorem pictures (CBTRN03C, CBSTM03A), controls with a
      * 9, 0 / right after the point, and pictures with no integer
      * digit position. IBM's result in each comment.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VEDITPT1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  T1 PIC Z(9).99-.
       01  T2 PIC -ZZZ,ZZZ,ZZZ.ZZ.
       01  T3 PIC +ZZZ,ZZZ,ZZZ.ZZ.
       01  T4 PIC 9(9).99-.
       01  P1 PIC $$,.99.
       01  P2 PIC ZZ,.99.
       01  P3 PIC **,.99.
       01  P4 PIC --,.99.
       01  P5 PIC Z,.ZZ.
       01  P6 PIC **B.99.
       01  P7 PIC $$B.99.
       01  P8 PIC ++,.99.
       01  P9 PIC $$,V99.
       01  PA PIC **,.**.
       01  PB PIC ZZ,B.99.
       01  PC PIC $$,$,.99CR.
       01  PD PIC *,**,.99-.
       01  C1 PIC Z9,.99.
       01  C2 PIC Z,ZZ9.99.
       01  C3 PIC $$9,.99.
       01  S1 PIC ZZ./99.
       01  S2 PIC $$.099.
       01  N1 PIC 0.ZZ.
       01  N2 PIC /.**.
       01  N3 PIC B.**.
       PROCEDURE DIVISION.
       P0.
      *    "         .00 " "         .05-" "-      1,234.50"
           MOVE 0 TO T1 DISPLAY 'E01 [' T1 ']'
           MOVE -0.05 TO T1 DISPLAY 'E02 [' T1 ']'
           MOVE -1234.5 TO T2 DISPLAY 'E03 [' T2 ']'
      *    "            .05" "+           .50" "000000000.05-"
           MOVE 0.05 TO T2 DISPLAY 'E04 [' T2 ']'
           MOVE 0.5 TO T3 DISPLAY 'E05 [' T3 ']'
           MOVE -0.05 TO T4 DISPLAY 'E06 [' T4 ']'
      *    "  $.00" "  $.05" "$1,.50"
           MOVE 0 TO P1 DISPLAY 'E07 [' P1 ']'
           MOVE 0.05 TO P1 DISPLAY 'E08 [' P1 ']'
           MOVE 1.5 TO P1 DISPLAY 'E09 [' P1 ']'
      *    "   .00" "12,.50" "***.86" "*7,.86"
           MOVE 0 TO P2 DISPLAY 'E10 [' P2 ']'
           MOVE 12.5 TO P2 DISPLAY 'E11 [' P2 ']'
           MOVE 0.86 TO P3 DISPLAY 'E12 [' P3 ']'
           MOVE 7.86 TO P3 DISPLAY 'E13 [' P3 ']'
      *    "  -.05" "   .05" "  .05" "     "
           MOVE -0.05 TO P4 DISPLAY 'E14 [' P4 ']'
           MOVE 0.05 TO P4 DISPLAY 'E15 [' P4 ']'
           MOVE 0.05 TO P5 DISPLAY 'E16 [' P5 ']'
           MOVE 0 TO P5 DISPLAY 'E17 [' P5 ']'
      *    "***.86" "  $.00" "  +.05" "  -.05" "  $05"
           MOVE 0.86 TO P6 DISPLAY 'E18 [' P6 ']'
           MOVE 0 TO P7 DISPLAY 'E19 [' P7 ']'
           MOVE 0.05 TO P8 DISPLAY 'E20 [' P8 ']'
           MOVE -0.05 TO P8 DISPLAY 'E21 [' P8 ']'
           MOVE 0.05 TO P9 DISPLAY 'E22 [' P9 ']'
      *    "***.05" "***.**" "    .05" "    $.05CR" "*****.05 "
           MOVE 0.05 TO PA DISPLAY 'E23 [' PA ']'
           MOVE 0 TO PA DISPLAY 'E24 [' PA ']'
           MOVE 0.05 TO PB DISPLAY 'E25 [' PB ']'
           MOVE -0.05 TO PC DISPLAY 'E26 [' PC ']'
           MOVE 0.05 TO PD DISPLAY 'E27 [' PD ']'
      *    controls: " 0,.05" "    0.05" " $0,.05"
           MOVE 0.05 TO C1 DISPLAY 'E28 [' C1 ']'
           MOVE 0.05 TO C2 DISPLAY 'E29 [' C2 ']'
           MOVE 0.05 TO C3 DISPLAY 'E30 [' C3 ']'
      *    0 and / right after the point stay: "  ./05" " $.005"
           MOVE 0.05 TO S1 DISPLAY 'E31 [' S1 ']'
           MOVE 0.05 TO S2 DISPLAY 'E32 [' S2 ']'
      *    no integer digit position (the string is right of the
      *    point): the character before the point is not part of it:
      *    "0.05" "/.05" " .05" "0.50"
           MOVE 0.05 TO N1 DISPLAY 'E33 [' N1 ']'
           MOVE 0.05 TO N2 DISPLAY 'E34 [' N2 ']'
           MOVE 0.05 TO N3 DISPLAY 'E35 [' N3 ']'
           MOVE 0.5 TO N1 DISPLAY 'E36 [' N1 ']'
           STOP RUN.
