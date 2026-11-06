      * EXPECT-FAULT: BLANK WHEN ZERO on N, which is not numeric-edited
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U20.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9(4) BLANK WHEN ZERO VALUE 0.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           DISPLAY N.
           STOP RUN.
