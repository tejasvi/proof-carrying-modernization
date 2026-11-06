       IDENTIFICATION DIVISION.
       PROGRAM-ID. GCIX.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  R1.
           05  L PIC X(3) VALUE 'lll'.
           05  D USAGE INDEX.
           05  N PIC 9 VALUE 1.
           05  K USAGE INDEX.
       01  R2.
           05  L PIC X(3) VALUE '---'.
           05  D PIC X(3) VALUE 'KMH'.
           05  N PIC 9 VALUE 3.
           05  K USAGE INDEX.
       01  T.
           05  TE PIC X OCCURS 3 INDEXED BY TI.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           SET TI TO 2.
           SET K OF R1 TO TI.
           MOVE CORRESPONDING R1 TO R2.
           DISPLAY 'L=' L OF R2 ' D=' D OF R2 ' N=' N OF R2.
           SET TI TO K OF R2.
           IF TI = 2 DISPLAY 'K MOVED' ELSE DISPLAY 'K NOT MOVED'.
           ADD CORRESPONDING R1 TO R2
               ON SIZE ERROR DISPLAY 'SIZE ERROR'
               NOT ON SIZE ERROR DISPLAY 'NO SIZE ERROR'
           END-ADD.
           DISPLAY 'N=' N OF R2.
           STOP RUN.
