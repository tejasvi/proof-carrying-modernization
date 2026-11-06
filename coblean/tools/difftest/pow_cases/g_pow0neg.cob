       IDENTIFICATION DIVISION.
       PROGRAM-ID. GPOW0N.
      * G-pow0neg: zero raised to a negative power is a size error
      * (IBM, SIZE ERROR phrases: the ON SIZE ERROR statement runs and
      * the receiver keeps its value); GnuCOBOL gives 0 and no size
      * error. Every Z line differs.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  NZ     PIC 9 VALUE 0.
       77  NM     PIC S9 VALUE -1.
       77  IA     PIC S99 VALUE 0.
       77  W0     PIC S9(5) VALUE 0.
       77  W1     PIC S9(5)V9 VALUE 0.
       77  E0     PIC -(5)9.
       77  E1     PIC -(5)9.9.
       PROCEDURE DIVISION.
           MOVE 77 TO W0.
           COMPUTE W0 = NZ ** NM
               ON SIZE ERROR DISPLAY 'Z01 Z|'
               NOT ON SIZE ERROR DISPLAY 'Z01 N|'
           END-COMPUTE.
           MOVE W0 TO E0. DISPLAY 'Z02 [' E0 ']'.
           MOVE 77 TO W1.
           COMPUTE W1 = IA ** (NM * 3) + 5
               ON SIZE ERROR DISPLAY 'Z03 Z|'
               NOT ON SIZE ERROR DISPLAY 'Z03 N|'
           END-COMPUTE.
           MOVE W1 TO E1. DISPLAY 'Z04 [' E1 ']'.
           STOP RUN.
