      * EXPECT-RUN
       IDENTIFICATION DIVISION.
       PROGRAM-ID. N07.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  T.
           05  TE PIC X OCCURS 3 INDEXED BY TI.
       77  X USAGE INDEX.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           SET TI TO 2.
           SET X TO TI.
           SET TI TO X.
           STOP RUN.
