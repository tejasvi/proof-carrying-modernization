       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWLO.
      * Such a power under a literal exponent (IBM takes the base's
      * integer places as 30 - dmax and holds that power with dmax
      * places too; the literal-exponent path computes it exactly):
      * unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  TWO    PIC 9 VALUE 2.
       77  DA     PIC S9V9 VALUE 1.5.
       77  W1     PIC S9(5)V9 VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W1 = (DA ** TWO) ** 2.
           DISPLAY 'R01 ' W1.
           STOP RUN.
