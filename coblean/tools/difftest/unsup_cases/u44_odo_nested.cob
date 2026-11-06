      * EXPECT-FAULT: OCCURS DEPENDING ON table T containing one
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U44.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9 VALUE 3.
       01  M PIC 9 VALUE 2.
       01  R.
           05  T OCCURS 1 TO 5 DEPENDING ON N.
               10  U OCCURS 1 TO 4 DEPENDING ON M PIC X.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           DISPLAY R.
           STOP RUN.
