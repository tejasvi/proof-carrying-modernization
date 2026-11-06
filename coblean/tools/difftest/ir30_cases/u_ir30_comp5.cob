       IDENTIFICATION DIVISION.
       PROGRAM-ID. UIR305.
      * ar2-fix hand case: COMP-5 items can hold more digits than their
      * PICTURE; the product of two 7.9 COMP-5 items has 18 decimal
      * places over dmax and 14 to 22 integer places: the places IBM
      * carries are open, unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  C5A      PIC S9(7)V9(9) COMP-5 VALUE 1.5.
       01  C5B      PIC S9(7)V9(9) COMP-5 VALUE 2.5.
       01  D5A      PIC S9(4) COMP-5 VALUE 15.
       01  X        PIC 9(9)V9(9) VALUE 0.
       01  Y        PIC 9(9)V9(9) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE X Y = D5A * D5A
           DISPLAY "V01 " X " " Y
           COMPUTE X Y = C5A * C5B
           DISPLAY "U01 " X " " Y
           STOP RUN.
