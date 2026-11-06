       IDENTIFICATION DIVISION.
       PROGRAM-ID. UIR30X.
      * ar2-fix hand case: FUNCTION MAX keeps its result in one field for
      * all arguments; an 18-digit integer and a 2.16 item need 34
      * digits together: unsupported (the cut of that field is open).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  L18      PIC 9(18) VALUE 12.
       01  F5       PIC S9(2)V9(16) VALUE 2.5.
       01  F1       PIC S9(9)V9(9) VALUE 2.5.
       01  X        PIC 9(18) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE X = FUNCTION MAX (L18 F1) + 1
           DISPLAY "V01 " X
           COMPUTE X = FUNCTION MAX (L18 F5) + 1
           DISPLAY "U01 " X
           STOP RUN.
