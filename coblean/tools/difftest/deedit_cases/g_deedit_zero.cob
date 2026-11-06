       IDENTIFICATION DIVISION.
       PROGRAM-ID. GDEEDZR.
      * G-deedit-zero: GnuCOBOL 3.2 reads a 0 insertion character as a
      * digit when it de-edits. '1230' in PIC 9(3)0 is the editing of
      * 123. Model (IBM): N1 123.00 '012300'; GnuCOBOL 1230.00 '123000'.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E1 PIC 9(3)0.
       01  N1 PIC 9(4)V99.
       01  N1X REDEFINES N1 PIC X(6).
       PROCEDURE DIVISION.
       P0.
           MOVE 123 TO E1
           MOVE E1 TO N1
           DISPLAY 'E1[' E1 '] N1[' N1X ']'
           STOP RUN.
