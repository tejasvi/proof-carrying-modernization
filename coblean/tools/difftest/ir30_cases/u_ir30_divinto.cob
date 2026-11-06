       IDENTIFICATION DIVISION.
       PROGRAM-ID. UIR30DI.
      * ar2-fix hand case: DIVIDE A INTO R ROUNDED without GIVING: each
      * receiver is a dividend, and its quotient, an intermediate result
      * under ROUNDED, can need 10 + 16 integer and 8 decimal places
      * (34): unsupported, as with GIVING.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A16      PIC 9(2)V9(16) VALUE 2.
       01  R8       PIC 9(10)V9(8) VALUE 7.
       01  S2       PIC 99 VALUE 4.
       01  R2       PIC 9(4)V99 VALUE 7.
       PROCEDURE DIVISION.
       P0.
           DIVIDE S2 INTO R2 ROUNDED
           DISPLAY "V01 " R2
           DIVIDE A16 INTO R8 ROUNDED
           DISPLAY "U01 " R8
           STOP RUN.
