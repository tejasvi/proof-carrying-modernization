       IDENTIFICATION DIVISION.
       PROGRAM-ID. GDEEDDB.
      * G-deedit-db: GnuCOBOL 3.2 ignores a DB sign when it de-edits.
      * '$ 45.60DB' is the editing of -45.60 (IBM: DB shows a negative
      * value). Model (IBM): N1 -45.60 '00456p'.
      * GnuCOBOL: +45.60 '004560'.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E1 PIC $ZZ9.99DB.
       01  N1 PIC S9(4)V99.
       01  N1X REDEFINES N1 PIC X(6).
       PROCEDURE DIVISION.
       P0.
           MOVE -45.6 TO E1
           MOVE E1 TO N1
           DISPLAY 'E1[' E1 '] N1[' N1X ']'
           STOP RUN.
