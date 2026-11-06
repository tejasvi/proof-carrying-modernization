       IDENTIFICATION DIVISION.
       PROGRAM-ID. UC30D.
      * ar2-fix hand case: DIVIDE A16 INTO E18 D15, the receiving items
      * E18 and D15: 18 + 15 = 33 digits: unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A16      PIC 9(16)V99 VALUE 1.5.
       01  D15      PIC 9(3)V9(15) VALUE 4.5.
       01  E18      PIC 9(18) VALUE 5.
       PROCEDURE DIVISION.
       P0.
           DISPLAY "V01 " E18
           DIVIDE A16 INTO E18 D15
           DISPLAY "U01 " E18 " " D15
           STOP RUN.
