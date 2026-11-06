      * EXPECT-REJECT: OCCURS DEPENDING ON object N is not an integer item outside every table
       IDENTIFICATION DIVISION.
       PROGRAM-ID. R10.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9V9 VALUE 3.
       01  R.
           05  T OCCURS 1 TO 5 DEPENDING ON N PIC X.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
