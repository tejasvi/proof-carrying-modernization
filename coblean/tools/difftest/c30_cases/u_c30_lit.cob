       IDENTIFICATION DIVISION.
       PROGRAM-ID. UC30L.
      * ar2-fix hand case: ADD 0000000000000001 TO D15, a literal of 16
      * digits as written and D15: 16 + 15 = 31 digits: unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  D15      PIC 9(3)V9(15) VALUE 4.5.
       PROCEDURE DIVISION.
       P0.
           DISPLAY "V01 " D15
           ADD 0000000000000001 TO D15
           DISPLAY "U01 " D15
           STOP RUN.
