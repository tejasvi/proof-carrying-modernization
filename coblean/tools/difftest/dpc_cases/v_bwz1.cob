       IDENTIFICATION DIVISION.
       PROGRAM-ID. P8B.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 B1 PIC 999 VALUE "000" BLANK WHEN ZERO.
       01 B2 PIC 9(4) BLANK WHEN ZERO.
       01 B6 PIC 9(5) VALUE "12 4X" BLANK WHEN ZERO.
       01 X1 PIC X(5).
       01 N1 PIC S9(3)V9 VALUE -12.5.
       PROCEDURE DIVISION.
           DISPLAY "Z01 [" B1 "] [" B6 "]|"
           MOVE 0 TO B1 DISPLAY "Z02 [" B1 "]|"
           MOVE 5 TO B1 DISPLAY "Z03 [" B1 "]|"
           MOVE -5 TO B1 DISPLAY "Z04 [" B1 "]|"
           MOVE 1234 TO B2 DISPLAY "Z05 [" B2 "]|"
           MOVE N1 TO B2 DISPLAY "Z06 [" B2 "]|"
           MOVE ZERO TO B2 DISPLAY "Z07 [" B2 "]|"
           MOVE B2 TO X1 DISPLAY "Z08 [" X1 "]|"
           COMPUTE B1 = 2 * 3 DISPLAY "Z09 [" B1 "]|"
           IF B1 = "006" DISPLAY "Z10 Y|" ELSE DISPLAY "Z10 N|"
           END-IF
           INITIALIZE B1 DISPLAY "Z11 [" B1 "]|"
           MOVE 1234 TO B1 DISPLAY "Z12 [" B1 "]|"
           ADD 1 TO N1 GIVING B2 DISPLAY "Z13 [" B2 "]|"
           MOVE 0.4 TO B2 DISPLAY "Z14 [" B2 "]|"
           STOP RUN.
