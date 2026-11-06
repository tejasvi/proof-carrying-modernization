       IDENTIFICATION DIVISION.
       PROGRAM-ID. GEDITLC.
      * G-editlc: GnuCOBOL 3.2 writes a ',' with no digit position on
      * its left as a space; IBM writes the ',' (a simple insertion
      * character left of any zero-suppression or floating string is
      * not part of it). Every line differs in that character only.
      * lctest.py --run.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  L01 PIC ,ZZ9.
       01  L02 PIC ,999.
       01  L03 PIC ,**9.
       01  L04 PIC ,$$9.
       01  L05 PIC ,++9.
       01  L06 PIC ,--9.
       01  L07 PICTURE IS ,ZZ9.99CR.
       01  L08 PIC ,9(3)V99.
       01  L09 PIC B,ZZ9.
       01  L10 PIC ,
      -        ZZ9.
       PROCEDURE DIVISION.
       P0.
           MOVE 5 TO L01 DISPLAY 'L01 5 [' L01 ']'
           MOVE 5 TO L02 DISPLAY 'L02 5 [' L02 ']'
           MOVE 5 TO L03 DISPLAY 'L03 5 [' L03 ']'
           MOVE 95 TO L04 DISPLAY 'L04 95 [' L04 ']'
           MOVE -5 TO L05 DISPLAY 'L05 -5 [' L05 ']'
           MOVE -5 TO L06 DISPLAY 'L06 -5 [' L06 ']'
           MOVE -5.25 TO L07 DISPLAY 'L07 -5.25 [' L07 ']'
           MOVE 1.5 TO L08 DISPLAY 'L08 1.5 [' L08 ']'
           MOVE 123 TO L09 DISPLAY 'L09 123 [' L09 ']'
           MOVE 5 TO L10 DISPLAY 'L10 5 [' L10 ']'
           STOP RUN.
