       IDENTIFICATION DIVISION.
       PROGRAM-ID. UIR30O.
      * ar2-fix hand case: ROUNDED ("one more integer [decimal] place
      * might be carried") with an intermediate result over 30 digits
      * whose decimal places exceed dmax: the places IBM carries are
      * open, the model stops, unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A9       PIC 9(9)V9(9) VALUE 1.123456789.
       01  B9       PIC 9(9)V9(9) VALUE 1.987654321.
       01  C8       PIC 9(8) VALUE 10000000.
       01  X9       PIC 9(8)V9(9) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE X9 ROUNDED = A9 * C8
           DISPLAY "V01 " X9
           COMPUTE X9 ROUNDED = A9 * B9 * C8
           DISPLAY "U01 " X9
           STOP RUN.
