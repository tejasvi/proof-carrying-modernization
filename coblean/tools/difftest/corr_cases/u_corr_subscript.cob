       IDENTIFICATION DIVISION.
       PROGRAM-ID. UCSB.
      * a receiver of MOVE CORRESPONDING is the subscript of the sender:
      * unsupported in the model (IBM: subscripts evaluated per pair or
      * once is not documented for CORRESPONDING).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  T.
           05  TE OCCURS 3.
               10  A PIC X.
               10  K PIC 9.
       01  G2.
           05  K PIC 9 VALUE 1.
           05  A PIC X VALUE '-'.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE 'a3b2c1' TO T.
           MOVE CORRESPONDING TE (K OF G2) TO G2.
           DISPLAY 'G2=' G2.
           STOP RUN.
