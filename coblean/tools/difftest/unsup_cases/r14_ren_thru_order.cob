      * EXPECT-REJECT: starts or ends before
       IDENTIFICATION DIVISION.
       PROGRAM-ID. R14.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  R.
           05  A PIC X(4).
           05  B PIC X(4).
       66  RBA RENAMES B THRU A.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
