       IDENTIFICATION DIVISION.
       PROGRAM-ID. UC30C.
      * ar2-fix hand case: ADD CORRESPONDING G1 TO G2, the pair X1 / X1
      * (9(16)V99 and 9(2)V9(16)): 16 + 16 = 32 digits: unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05  X1   PIC 9(16)V99 VALUE 1.5.
           05  Y1   PIC 9(15)V9(3) VALUE 1.
       01  G2.
           05  X1   PIC 9(2)V9(16) VALUE 2.25.
           05  Y1   PIC 9(3)V9(15) VALUE 2.
       PROCEDURE DIVISION.
       P0.
           DISPLAY "V01 " Y1 OF G2
           ADD CORRESPONDING G1 TO G2
           DISPLAY "U01 " Y1 OF G2
           STOP RUN.
