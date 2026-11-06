       IDENTIFICATION DIVISION.
       PROGRAM-ID. ILEAD0.
      * '012.34' in PIC ZZ9.99: editing never leaves a leading zero in
      * a Z position, so no value edits to it: the model stops
      * (invalidData); GnuCOBOL moves 12.34.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E1 PIC ZZ9.99.
       01  E1X REDEFINES E1 PIC X(6).
       01  N1 PIC S9(4)V99.
       01  N1X REDEFINES N1 PIC X(6).
       PROCEDURE DIVISION.
       P0.
           MOVE 12.34 TO E1
           MOVE E1 TO N1
           DISPLAY 'E1[' E1 '] N1[' N1X ']'
           MOVE '0' TO E1X (1:1)
           DISPLAY 'E1[' E1 ']'
           MOVE E1 TO N1
           DISPLAY 'N1[' N1X ']'
           STOP RUN.
