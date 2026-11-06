       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWFA.
      * A power inside a function argument (IBM computes an argument
      * with its own dmax): unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  TWO    PIC 9 VALUE 2.
       77  IA     PIC S99 VALUE 4.
       77  W1     PIC S9(5)V9 VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W1 = FUNCTION MAX(IA ** TWO, 1).
           DISPLAY 'R01 ' W1.
           STOP RUN.
