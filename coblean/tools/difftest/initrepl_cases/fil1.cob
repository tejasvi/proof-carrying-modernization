      * FILLER items without a separate sign: skipped by plain INITIALIZE
      * and by REPLACING on both sides (IBM rule 1a).
      * Run: filetest.py --run fil1.cob (6/6 lines agree).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. FIL1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G.
           05 GA PIC X(2).
           05 FILLER PIC X(2).
           05 GB PIC 9(2).
           05 FILLER PIC 9(2).
           05 PIC X(2).
           05 GC PIC A(2).
           05 FILLER PIC A(2).
           05 GD PIC X0X.
           05 FILLER PIC X0X.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE ALL '#' TO G
           INITIALIZE G
           DISPLAY '1 [' G ']'
           MOVE ALL '#' TO G
           INITIALIZE G REPLACING NUMERIC BY 5
           DISPLAY '2 [' G ']'
           MOVE ALL '#' TO G
           INITIALIZE G REPLACING ALPHANUMERIC BY 'Z'
           DISPLAY '3 [' G ']'
           MOVE ALL '#' TO G
           INITIALIZE G REPLACING ALPHABETIC BY 'Q'
           DISPLAY '4 [' G ']'
           MOVE ALL '#' TO G
           INITIALIZE G REPLACING ALPHANUMERIC-EDITED BY 'KL'
           DISPLAY '5 [' G ']'
           MOVE ALL '#' TO G
           INITIALIZE G REPLACING NUMERIC BY 7 ALPHANUMERIC BY 'Y'
           DISPLAY '6 [' G ']'
           STOP RUN.
