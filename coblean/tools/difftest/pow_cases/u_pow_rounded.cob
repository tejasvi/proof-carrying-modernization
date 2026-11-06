       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWRD.
      * COMPUTE ROUNDED with an exponent that is a data item: IBM
      * "might" carry one more decimal place; the front end keeps it
      * unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  TWO    PIC 9 VALUE 2.
       77  DA     PIC S9V9 VALUE 1.5.
       77  W1     PIC S9(5)V9 VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W1 ROUNDED = DA ** TWO.
           DISPLAY 'R01 ' W1.
           STOP RUN.
