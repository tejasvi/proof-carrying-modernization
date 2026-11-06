       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWDV.
      * A division in the exponent (IBM: floating point when dmax is
      * greater than 0): unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  TWO    PIC 9 VALUE 2.
       77  IA     PIC S99 VALUE 4.
       77  W1     PIC S9(5)V9 VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W1 = IA ** (TWO / 2).
           DISPLAY 'R01 ' W1.
           STOP RUN.
