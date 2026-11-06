       IDENTIFICATION DIVISION.
       PROGRAM-ID. VDPC1.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           CURRENCY SIGN IS "W"
           DECIMAL-POINT IS COMMA.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 N1 PIC 9(4)V99 VALUE 1234,56.
       01 N2 PIC S9(5)V99 VALUE -12,5.
       01 N3 PIC 9(3)V9(3) VALUE ,125.
       01 E1 PIC 9.999.999,99.
       01 E2 PIC ZZ.ZZZ,99.
       01 E3 PIC **.***,99.
       01 E4 PIC Z.ZZZ,ZZ.
       01 E5 PIC *.***,**.
       01 E6 PIC WWWWW.
       01 E7 PIC W9999.
       01 E8 PIC W.WWW,99.
       01 E9 PIC -ZZ9,99.
       01 EA PIC +ZZ9,99.
       01 EB PIC ZZ9,99CR.
       01 EK PIC ZZ9,99DB.
       01 ED PIC 99B99,9.
       01 EE PIC 99/99.
       01 EF PIC 990,99.
       01 EG PIC ZZZ,99 BLANK WHEN ZERO.
       01 EH PIC --.--9,99.
       01 EI PIC WW.WW9,99.
       01 EJ PIC ZZZ.ZZZ.
       01 N4 PIC 9(5)V99.
       PROCEDURE DIVISION.
           DISPLAY "D01 " N1 " " N3
           MOVE N1 TO E1 DISPLAY "D02 " E1
           MOVE N1 TO E2 DISPLAY "D03 " E2
           MOVE 0,05 TO E2 DISPLAY "D04 " E2
           MOVE 0 TO E2 DISPLAY "D05 " E2
           MOVE 12,3 TO E3 DISPLAY "D06 " E3
           MOVE 0 TO E3 DISPLAY "D07 " E3
           MOVE 0 TO E4 DISPLAY "D08 [" E4 "]"
           MOVE 0,01 TO E4 DISPLAY "D09 [" E4 "]"
           MOVE 0 TO E5 DISPLAY "D10 " E5
           MOVE 1,5 TO E5 DISPLAY "D11 " E5
           MOVE 42 TO E6 DISPLAY "D12 [" E6 "]"
           MOVE 0 TO E6 DISPLAY "D13 [" E6 "]"
           MOVE 42 TO E7 DISPLAY "D14 " E7
           MOVE 5,25 TO E8 DISPLAY "D16 " E8
           MOVE -12,34 TO E9 DISPLAY "D17 " E9
           MOVE 12,34 TO EA DISPLAY "D18 " EA
           MOVE -1,5 TO EA DISPLAY "D19 " EA
           MOVE -12,34 TO EB DISPLAY "D20 " EB
           MOVE -12,34 TO EK DISPLAY "D21 " EK
           MOVE 1234,5 TO ED DISPLAY "D22 " ED
           MOVE 1234 TO EE DISPLAY "D23 " EE
           MOVE 12,34 TO EF DISPLAY "D24 " EF
           MOVE 0 TO EG DISPLAY "D25 [" EG "]"
           MOVE 1,5 TO EG DISPLAY "D26 [" EG "]"
           MOVE -1234,5 TO EH DISPLAY "D27 [" EH "]"
           MOVE 1234,5 TO EI DISPLAY "D28 [" EI "]"
           MOVE 1234567 TO EJ DISPLAY "D29 [" EJ "]"
           COMPUTE N4 = 1,5 * 2 + N1
           DISPLAY "D31 " N4
           IF N1 = 1234,56 DISPLAY "D32 Y" ELSE DISPLAY "D32 N"
           END-IF
           IF N1 > 1234,559 DISPLAY "D33 Y" ELSE DISPLAY "D33 N"
           END-IF
           MOVE N1 TO E2
           ADD 0,5 TO N1 GIVING E2 DISPLAY "D36 " E2
           STOP RUN.
