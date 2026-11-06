      * EXPECT-RUN
      * (u04's program: one CURRENCY SIGN of one character is modelled)
       IDENTIFICATION DIVISION.
       PROGRAM-ID. N21.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           CURRENCY SIGN IS 'L'.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E PIC LLL9.99.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE 12.5 TO E.
           DISPLAY '[' E ']'.
           STOP RUN.
