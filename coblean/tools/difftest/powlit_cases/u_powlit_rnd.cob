       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWLR.
      * ar2-fix hand case: ROUNDED ("one more integer [decimal] place
      * might be carried") with a power by a literal of 28 or more
      * digits (S2 ** 14: i 28): which row of IBM's exponentiation table
      * applies is open; unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  S2       PIC 99 VALUE 7.
       01  S1       PIC S9(3)V99 VALUE 1.5.
       01  R9       PIC 9(17)V9 VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE R9 ROUNDED = S1 ** 3
           DISPLAY "V01 " R9
           COMPUTE R9 ROUNDED = S2 ** 14
           DISPLAY "U01 " R9
           STOP RUN.
