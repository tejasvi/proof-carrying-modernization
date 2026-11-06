      * M-editlead (fixed): a simple insertion character LEFT of a
      * zero-suppression or floating string (before its first symbol)
      * is not part of the string (IBM: only those "within or to the
      * immediate right of the string" are) and is written; one inside
      * a floating string, after its first symbol, is part of it.
      * GnuCOBOL agrees. IBM's result in each comment.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VEDITLD.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E1 PIC 0ZZ.99.
       01  E2 PIC /**.99.
       01  E3 PIC 0$$.99.
       01  E4 PIC +0ZZ.99.
       01  E5 PIC $0ZZ.99.
       01  E6 PIC B**.99.
       01  E7 PIC $,$$.99.
       01  E8 PIC 0--9.99.
       PROCEDURE DIVISION.
       P0.
      *    "0 5.50" "0  .05" "/*5.50" "0$5.50" "+0 5.50" "$0 5.50"
           MOVE 5.5 TO E1 DISPLAY 'L01 [' E1 ']'
           MOVE 0.05 TO E1 DISPLAY 'L02 [' E1 ']'
           MOVE 5.5 TO E2 DISPLAY 'L03 [' E2 ']'
           MOVE 5.5 TO E3 DISPLAY 'L04 [' E3 ']'
           MOVE 5.5 TO E4 DISPLAY 'L05 [' E4 ']'
           MOVE 5.5 TO E5 DISPLAY 'L06 [' E5 ']'
      *    " *5.50" "0 $.05" " $12.50" "   $.05"
           MOVE 5.5 TO E6 DISPLAY 'L07 [' E6 ']'
           MOVE 0.05 TO E3 DISPLAY 'L08 [' E3 ']'
           MOVE 12.5 TO E7 DISPLAY 'L09 [' E7 ']'
           MOVE 0.05 TO E7 DISPLAY 'L10 [' E7 ']'
      *    "0 -1.50" "0  3.00"
           MOVE -1.5 TO E8 DISPLAY 'L11 [' E8 ']'
           MOVE 3 TO E8 DISPLAY 'L12 [' E8 ']'
           STOP RUN.
