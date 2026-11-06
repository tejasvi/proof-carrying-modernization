       IDENTIFICATION DIVISION.
       PROGRAM-ID. VC301.
      * ar2-fix hand case: arithmetic statements whose composite of
      * operands (IBM, Language Reference, "Arithmetic statement
      * operands") is 30 digits or fewer: accepted and run.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A16      PIC 9(16)V99 VALUE 1.5.
       01  B16      PIC 9(2)V9(16) VALUE 2.25.
       01  C15      PIC 9(15)V9(3) VALUE 3.125.
       01  D15      PIC 9(3)V9(15) VALUE 4.5.
       01  E18      PIC 9(18) VALUE 5.
       01  F12      PIC 9(6)V9(12) VALUE 6.75.
       01  M5       PIC 9(3)V99 VALUE 7.25.
       01  N2       PIC 99 VALUE 3.
       PROCEDURE DIVISION.
       P0.
      * K01 ADD C15 TO D15: 15 integer + 15 decimal places = 30
           ADD C15 TO D15
           DISPLAY "K01 " D15
      * K02 the receiver after GIVING is not an operand: 16 + 3
           ADD A16 C15 GIVING D15
           DISPLAY "K02 " D15
      * K03 a literal of 15 digits as written and D15: 15 + 15
           ADD 000000000000001 TO D15
           DISPLAY "K03 " D15
      * K04 SUBTRACT C15 FROM D15: 30
           SUBTRACT C15 FROM D15
           DISPLAY "K04 " D15
      * K05 SUBTRACT ... FROM ... GIVING: A16 and C15, 16 + 3
           SUBTRACT A16 FROM C15 GIVING B16
           DISPLAY "K05 " B16
      * K06 MULTIPLY: the receiving items E18 and F12, 18 + 12
           MULTIPLY A16 BY E18 F12
           DISPLAY "K06 " E18 " " F12
      * K07 MULTIPLY ... GIVING one receiver: 15 + 3
           MULTIPLY A16 BY B16 GIVING C15
           DISPLAY "K07 " C15
      * K08 DIVIDE ... INTO two receivers: 18 + 12
           DIVIDE A16 INTO E18 F12
           DISPLAY "K08 " E18 " " F12
      * K09 the REMAINDER item is not an operand: E18 alone, 18
           DIVIDE M5 BY N2 GIVING E18 REMAINDER D15
           DISPLAY "K09 " E18 " " D15
           STOP RUN.
