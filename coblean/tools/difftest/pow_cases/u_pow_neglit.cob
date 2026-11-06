       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWNL.
      * A negative literal exponent (IBM's rule for literals differs
      * from that for data items): unsupported, as before.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  IA     PIC S99 VALUE 4.
       77  W1     PIC S9(5)V9 VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W1 = IA ** -2.
           DISPLAY 'R01 ' W1.
           STOP RUN.
