       IDENTIFICATION DIVISION.
       PROGRAM-ID. UC30M.
      * ar2-fix hand case: MULTIPLY A16 BY B16 GIVING E18 D15, the
      * receiving items E18 and D15: 18 + 15 = 33 digits: unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A16      PIC 9(16)V99 VALUE 1.5.
       01  B16      PIC 9(2)V9(16) VALUE 2.25.
       01  D15      PIC 9(3)V9(15) VALUE 4.5.
       01  E18      PIC 9(18) VALUE 5.
       PROCEDURE DIVISION.
       P0.
           DISPLAY "V01 " E18
           MULTIPLY A16 BY B16 GIVING E18 D15
           DISPLAY "U01 " E18 " " D15
           STOP RUN.
