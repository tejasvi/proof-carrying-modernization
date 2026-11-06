       IDENTIFICATION DIVISION.
       PROGRAM-ID. UC30SG.
      * ar2-fix hand case: SUBTRACT A16 FROM B16 GIVING C15, operands
      * A16 and B16: 16 + 16 = 32 digits: unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A16      PIC 9(16)V99 VALUE 1.5.
       01  B16      PIC 9(2)V9(16) VALUE 2.25.
       01  C15      PIC 9(15)V9(3) VALUE 3.125.
       PROCEDURE DIVISION.
       P0.
           DISPLAY "V01 " C15
           SUBTRACT A16 FROM B16 GIVING C15
           DISPLAY "U01 " C15
           STOP RUN.
