      * EXPECT-REJECT: cannot rename the level-01 entry
       IDENTIFICATION DIVISION.
       PROGRAM-ID. R12.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  R.
           05  A PIC X(4).
       66  RR RENAMES R.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
