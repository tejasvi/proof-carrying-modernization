       IDENTIFICATION DIVISION.
       PROGRAM-ID. P9.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  R1.
           05  A        PIC X(2) VALUE 'aa'.
           05  B        PIC X(2) VALUE 'bb'.
       66  X RENAMES A THRU B.
       66  Y RENAMES B.
       01  R2.
           05  X        PIC X(4) VALUE '----'.
           05  Y        PIC X(2) VALUE '--'.
           05  A        PIC X(2) VALUE '--'.
       01  R3.
           05  N1       PIC S9(3) VALUE -5.
           05  N2       PIC 9(2)V9 VALUE 1.5.
       66  NN RENAMES N1.
       01  R4.
           05  N1       PIC S9(3) VALUE 5.
           05  NN       PIC S9(3) VALUE 100.
           05  N2       PIC 9(2)V9 VALUE 2.
       PROCEDURE DIVISION.
       P0.
           MOVE CORRESPONDING R1 TO R2.
           DISPLAY 'R2=' R2 '.'.
           ADD CORRESPONDING R3 TO R4.
           DISPLAY 'R4=' R4 '.'.
           ADD CORR R3 TO R4 ON SIZE ERROR DISPLAY 'NEVER'.
           DISPLAY 'R4=' R4 '.'.
           STOP RUN.
