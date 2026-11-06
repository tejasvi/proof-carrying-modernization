       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWDE.
      * An exponent with decimal places (IBM: floating point):
      * unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  IA     PIC S99 VALUE 4.
       77  DA     PIC S9V9 VALUE 0.5.
       77  W1     PIC S9(5)V9 VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W1 = IA ** DA.
           DISPLAY 'R01 ' W1.
           STOP RUN.
