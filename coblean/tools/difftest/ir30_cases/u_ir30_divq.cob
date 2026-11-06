       IDENTIFICATION DIVISION.
       PROGRAM-ID. UIR30D.
      * ar2-fix hand case: DIVIDE with two GIVING receivers holds the
      * quotient as an intermediate result; L16 / F5 can need 16 + 16
      * integer places: unsupported (the statement).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  L16      PIC S9(16) VALUE 12345.
       01  F5       PIC S9(2)V9(16) VALUE 2.5.
       01  Q1       PIC 9(17) VALUE 0.
       01  Q2       PIC 9(17) VALUE 0.
       01  S1       PIC S9(3)V99 VALUE 2.5.
       PROCEDURE DIVISION.
       P0.
           DIVIDE L16 BY S1 GIVING Q1 Q2
           DISPLAY "V01 " Q1 " " Q2
           DIVIDE L16 BY F5 GIVING Q1 Q2
           DISPLAY "U01 " Q1 " " Q2
           STOP RUN.
