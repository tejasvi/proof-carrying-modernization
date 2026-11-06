      * EXPECT-FAULT: variably located items after the OCCURS DEPENDING ON table T
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U40.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9 VALUE 3.
       01  R.
           05  T OCCURS 1 TO 5 DEPENDING ON N PIC X.
           05  Z PIC XXX.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           DISPLAY Z.
           STOP RUN.
