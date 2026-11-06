       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWIF.
      * FUNCTION INTEGER of an argument with decimal places in the
      * COMPUTE (IBM's dmax counts no places for an integer function,
      * the resolver counts its argument's): unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  TWO    PIC 9 VALUE 2.
       77  DA     PIC S9V9 VALUE 1.5.
       77  DB     PIC S9V99 VALUE 1.25.
       77  W1     PIC S9(5)V9 VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W1 = DA ** TWO + FUNCTION INTEGER(DB).
           DISPLAY 'R01 ' W1.
           STOP RUN.
