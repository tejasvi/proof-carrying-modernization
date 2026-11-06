      * EXPECT-RUN
      * (BLANK WHEN ZERO on an unsigned numeric item: numeric-edited)
       IDENTIFICATION DIVISION.
       PROGRAM-ID. N23.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9(4) BLANK WHEN ZERO VALUE '0000'.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE 0 TO N.
           DISPLAY '[' N ']'.
           STOP RUN.
