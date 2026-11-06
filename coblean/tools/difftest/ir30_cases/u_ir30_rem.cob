       IDENTIFICATION DIVISION.
       PROGRAM-ID. UIR30R.
      * ar2-fix hand case: the first step of FUNCTION REM, L18 / F5, can
      * need 18 + 16 integer places; L18 1E17 by F5 1E-16 has 34 digits:
      * IBM cuts nonzero digits of that quotient (IGZ0036W): stop.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  L18      PIC 9(18) VALUE 100000000000000000.
       01  F5       PIC S9(2)V9(16) VALUE 0.0000000000000001.
       01  X0       PIC 9(18) VALUE 0.
       01  X        PIC 9(2)V9(16) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE X0 = FUNCTION REM (L18, 7)
           DISPLAY "V01 " X0
           COMPUTE X = FUNCTION REM (L18, F5)
           DISPLAY "U01 " X
           STOP RUN.
