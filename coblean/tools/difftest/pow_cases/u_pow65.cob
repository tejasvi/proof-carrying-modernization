       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOW65.
      * An exponent value of more than 64: the model stops with
      * unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  ONE    PIC 9 VALUE 1.
       77  N65    PIC 99 VALUE 65.
       77  W0     PIC S9(5) VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W0 = ONE ** N65.
           DISPLAY 'R01 ' W0.
           STOP RUN.
