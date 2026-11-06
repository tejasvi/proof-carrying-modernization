      * EXPECT-FAULT: RENAMES of the index data item IX
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U46.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  R.
           05  A PIC X(4).
           05  IX USAGE INDEX.
       66  RX RENAMES IX.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
