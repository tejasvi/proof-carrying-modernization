      * EXPECT-FAULT: index data item RX in the scope of a REDEFINES
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U25.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A PIC X(8).
       01  R REDEFINES A.
           05  RX USAGE INDEX.
           05  RB PIC X(4).
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
