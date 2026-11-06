       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWLC.
      * ar2-fix hand case: L1 ** 2 (i 32 > 30) is held with dmax (0)
      * decimal and 30 integer places; 9999999999999999 ** 2 has 32
      * digits: IBM cuts nonzero digits (a message); unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  L1       PIC S9(16) VALUE 9999999999999999.
       01  L1S      PIC S9(16) VALUE 99999.
       01  X18      PIC 9(18) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE X18 = L1S ** 2 + 1
           DISPLAY "V01 " X18
           COMPUTE X18 = L1 ** 2 + 1
           DISPLAY "U01 " X18
           STOP RUN.
