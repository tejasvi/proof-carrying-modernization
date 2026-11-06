       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWED.
      * A numeric-edited receiver (the resolver's dmax does not count
      * its decimal places): unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  TWO    PIC 9 VALUE 2.
       77  DA     PIC S9V9 VALUE 1.5.
       77  E2     PIC -(5)9.99.
       PROCEDURE DIVISION.
           COMPUTE E2 = DA ** TWO.
           DISPLAY 'R01 ' E2.
           STOP RUN.
