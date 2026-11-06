      * Index data items: the 4 bytes of an index data item place the
      * fields after it (LENGTH OF, and a REDEFINES view of the field
      * after it, which shares no byte with it); INITIALIZE of a group
      * holding one initializes the other fields and, as IBM specifies
      * (not a valid MOVE receiver), leaves the index data item alone.
      * GnuCOBOL agrees on every line but the two marked G-initindex,
      * where it shows 0 (it sets index data items to 0); the model
      * shows 3 and 4.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. IXLAY.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  TA.
           05  TAE PIC XX OCCURS 6 INDEXED BY IA.
       01  R.
           05  A PIC X VALUE "a".
           05  X USAGE INDEX.
           05  B PIC X(3) VALUE "bcd".
       01  R2 REDEFINES R.
           05  FILLER PIC X(5).
           05  B2 PIC X(3).
       01  T.
           05  TE OCCURS 3.
               10  TC PIC X VALUE "t".
               10  TX USAGE INDEX.
       01  N PIC 9(4).
       PROCEDURE DIVISION.
           MOVE LENGTH OF R TO N
           DISPLAY 'LEN R ' N
           MOVE LENGTH OF T TO N
           DISPLAY 'LEN T ' N
           MOVE LENGTH OF X TO N
           DISPLAY 'LEN X ' N
           MOVE 'xyz' TO B
           DISPLAY 'B2 ' B2
           SET IA TO 3
           SET X TO IA
           SET IA TO 4
           SET TX (2) TO IA
           INITIALIZE R T
           DISPLAY 'R [' A '][' B '] T [' TC (1) TC (2) TC (3) ']'
           SET IA TO X
           SET N TO IA
           DISPLAY 'X ' N ' G-initindex'
           SET IA TO TX (2)
           SET N TO IA
           DISPLAY 'TX2 ' N ' G-initindex'
           STOP RUN.
