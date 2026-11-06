      * VALUE ALL ZERO(S/ES) on numeric items (IBM: "When literal is a
      * figurative constant, the word ALL has no meaning"; ZERO may stand
      * for a numeric literal), level 88 included, every numeric usage.
      * Run: filetest.py --run vallzero1.cob (both sides, line by line).
      * Control: the front end of coblean-20261027T0518Z rejects it
      * ("nonnumeric VALUE for a numeric item"). Planted fault (recipe):
      * datadiv.py value_json returning {"fig": {"f": {"all": {"bs":
      * [48]}}}} (character zeros) for ALL ZERO makes N3, N4 and N7 differ.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VALLZ1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G.
           05 N1 PIC 999 VALUE ALL ZEROS.
           05 N1X REDEFINES N1 PIC XXX.
           05 N2 PIC S9(3)V9 VALUE ALL ZEROES.
           05 N2X REDEFINES N2 PIC X(4).
           05 N3 PIC S9(5) COMP-3 VALUE ALL ZERO.
           05 N3X REDEFINES N3 PIC X(3).
           05 N4 PIC 9(4) COMP VALUE ALL ZEROS.
           05 N4X REDEFINES N4 PIC X(2).
           05 N5 PIC S9(3) SIGN LEADING SEPARATE VALUE ALL ZEROS.
           05 N5X REDEFINES N5 PIC X(4).
           05 N6 PIC 99 VALUE ALL ZEROS.
              88 N6-ZERO VALUE ALL ZEROS.
              88 N6-ONE VALUE 1.
           05 X1 PIC XXX VALUE ALL ZEROS.
           05 E1 PIC ZZ9.99 VALUE ALL ZEROS.
           05 N7 PIC S9(4) COMP-5 VALUE ALL ZEROES.
           05 N7X REDEFINES N7 PIC X(2).
           05 N9 PIC 9(2) VALUE ALL ZEROS.
       PROCEDURE DIVISION.
       MAIN-PARA.
           DISPLAY 'N1X [' N1X '] N2X [' N2X '] N5X [' N5X ']'
           DISPLAY 'X1 [' X1 '] E1 [' E1 ']'
           IF N3X = X'00000C' DISPLAY 'N3 X00000C' ELSE
              DISPLAY 'N3 OTHER' END-IF
           IF N4X = X'0000' DISPLAY 'N4 X0000' ELSE
              DISPLAY 'N4 OTHER' END-IF
           IF N7X = X'0000' DISPLAY 'N7 X0000' ELSE
              DISPLAY 'N7 OTHER' END-IF
           IF N1 = 0 AND N2 = 0 AND N3 = 0 AND N4 = 0 AND N5 = 0
              AND N7 = ZERO AND N9 = ZEROS
              DISPLAY 'ALL ZERO' ELSE DISPLAY 'NOT ALL ZERO' END-IF
           IF N6-ZERO DISPLAY 'N6-ZERO TRUE' ELSE DISPLAY 'N6-ZERO F'
           END-IF
           ADD 1 TO N6
           IF N6-ZERO DISPLAY 'N6-ZERO TRUE' ELSE DISPLAY 'N6-ZERO F'
           END-IF
           IF N6-ONE DISPLAY 'N6-ONE TRUE' ELSE DISPLAY 'N6-ONE F'
           END-IF
           ADD 1 TO N1 N2 N3 N4 N5 N7
           DISPLAY 'N1X [' N1X '] N2X [' N2X '] N5X [' N5X ']'
           IF N3X = X'00001C' DISPLAY 'N3 X00001C' ELSE
              DISPLAY 'N3 OTHER' END-IF
           STOP RUN.
