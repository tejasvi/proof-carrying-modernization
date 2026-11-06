      * EXPECT-FAULT: OCCURS DEPENDING ON table T inside a table
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U41.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9 VALUE 3.
       01  R.
           05  ROW OCCURS 2.
               10  T OCCURS 1 TO 5 DEPENDING ON N PIC X.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           DISPLAY T(1, 1).
           STOP RUN.
