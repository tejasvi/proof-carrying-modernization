       IDENTIFICATION DIVISION.
       PROGRAM-ID. UIR30N.
      * ar2-fix hand case: ROUNDED "might" carry one more integer and
      * decimal place for each intermediate result, so the places grow
      * with each operation: ((F2 + F4) * S1) - F6 has 27 digits by the
      * table, up to 33 with those places: the places IBM carries are
      * open, the model stops, unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  F2       PIC 9(14)V9(4) VALUE 12.5.
       01  F4       PIC S9(12)V9(6) VALUE 3.25.
       01  S1       PIC S9(3)V99 VALUE 2.
       01  F6       PIC S9(16)V99 VALUE 1.5.
       01  R9       PIC 9(9)V9(9) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE R9 ROUNDED = (F2 + F4) * S1
           DISPLAY "V01 " R9
           COMPUTE R9 ROUNDED = ((F2 + F4) * S1) - F6
           DISPLAY "U01 " R9
           STOP RUN.
