      * EXPECT-REJECT: $ is not a currency symbol of this program
       IDENTIFICATION DIVISION.
       PROGRAM-ID. R21.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           CURRENCY SIGN IS 'W'.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E PIC $$9.99.
       PROCEDURE DIVISION.
           STOP RUN.
