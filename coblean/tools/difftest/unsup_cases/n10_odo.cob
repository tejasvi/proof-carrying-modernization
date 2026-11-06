      * EXPECT-RUN
       IDENTIFICATION DIVISION.
       PROGRAM-ID. N10.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9 VALUE 3.
       01  R.
           05  H PIC X VALUE 'H'.
           05  T OCCURS 1 TO 5 DEPENDING ON N PIC X.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE 'ABC' TO R.
           DISPLAY R.
           STOP RUN.
