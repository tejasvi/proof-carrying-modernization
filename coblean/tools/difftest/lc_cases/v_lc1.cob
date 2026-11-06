       IDENTIFICATION DIVISION.
       PROGRAM-ID. VLC1.
      * DECIMAL-POINT IS COMMA: a PICTURE string that begins with a
      * comma begins with the decimal point (lctest.py --run; every line
      * agrees with GnuCOBOL).
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           DECIMAL-POINT IS COMMA.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  D01 PIC ,99.
       01  D02 PICTURE IS ,999.
       01  D03 PIC ,9(4).
       01  D04 PIC ,ZZ.
       01  D05 PIC ,**.
       01  D06 PIC ,99+.
       01  D07 PIC ,99CR.
       01  D08 PIC ,99 BLANK WHEN ZERO.
       01  D09 PIC IS ,9B9.
       01  D10 PICTURE ,99-.
       01  N1 PIC S9(5)V9(4).
       01  N1X REDEFINES N1 PIC X(9).
       PROCEDURE DIVISION.
       P0.
           MOVE 0,5 TO D01 DISPLAY 'P01 0,5 [' D01 ']'
           MOVE 0,07 TO D01 DISPLAY 'P02 0,07 [' D01 ']'
           MOVE 0,125 TO D02 DISPLAY 'P03 0,125 [' D02 ']'
           MOVE 0,0042 TO D03 DISPLAY 'P04 0,0042 [' D03 ']'
           MOVE 0 TO D04 DISPLAY 'P05 0 [' D04 ']'
           MOVE 0,05 TO D04 DISPLAY 'P06 0,05 [' D04 ']'
           MOVE 0 TO D05 DISPLAY 'P07 0 [' D05 ']'
           MOVE 0,5 TO D05 DISPLAY 'P08 0,5 [' D05 ']'
           MOVE -0,25 TO D06 DISPLAY 'P09 -0,25 [' D06 ']'
           MOVE 0,25 TO D06 DISPLAY 'P10 0,25 [' D06 ']'
           MOVE -0,25 TO D07 DISPLAY 'P11 -0,25 [' D07 ']'
           MOVE 0 TO D08 DISPLAY 'P12 0 [' D08 ']'
           MOVE 0,75 TO D08 DISPLAY 'P13 0,75 [' D08 ']'
           MOVE 0,75 TO D09 DISPLAY 'P14 0,75 [' D09 ']'
           MOVE -0,5 TO D10 DISPLAY 'P15 -0,5 [' D10 ']'
           MOVE D10 TO N1 DISPLAY 'P16 D10 to N1 [' N1X ']'
           MOVE D03 TO N1 DISPLAY 'P17 D03 to N1 [' N1X ']'
           STOP RUN.
