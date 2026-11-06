      * Unsupported statement: DISPLAY of a numeric literal with
      * decimal places under DECIMAL-POINT IS COMMA (the model writes
      * 1.5 without the clause, GnuCOBOL 15 with and without it; IBM
      * gives no rule).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UDPCD.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           DECIMAL-POINT IS COMMA.
       PROCEDURE DIVISION.
           DISPLAY "D01 " 1,5 "|"
           STOP RUN.
