       IDENTIFICATION DIVISION.
       PROGRAM-ID. UC30A.
      * ar2-fix hand case: ADD A16 TO B16, a composite of operands of
      * 16 integer + 16 decimal places = 32 digits: unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A16      PIC 9(16)V99 VALUE 1.5.
       01  B16      PIC 9(2)V9(16) VALUE 2.25.
       PROCEDURE DIVISION.
       P0.
           DISPLAY "V01 " B16
           ADD A16 TO B16
           DISPLAY "U01 " B16
           STOP RUN.
