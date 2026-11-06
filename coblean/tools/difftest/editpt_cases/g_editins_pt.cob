      * G-editins (GnuCOBOL 3.2 departs from IBM): a 0 or / insertion
      * character inside or right after a zero-suppression or floating
      * string is part of the string (IBM: "Any simple insertion symbols
      * (B 0 / ,) within or to the immediate right of the string ... are
      * considered part of the string"), so it is replaced where the
      * string's leading zeros are; GnuCOBOL writes it. Here right
      * before the decimal point (the M-editpoint shape) and inside.
      * IBM's result in each comment (the model's); I05 I06 agree.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GEDITINS.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E1 PIC ZZ/V99.
       01  E2 PIC $$/.99.
       01  E3 PIC **0.99.
       01  E4 PIC $ZZ/,ZZZ.
       PROCEDURE DIVISION.
       P0.
      *    "   05" "  $.00" "***.86" "$      8"
           MOVE 0.05 TO E1 DISPLAY 'I01 [' E1 ']'
           MOVE 0 TO E2 DISPLAY 'I02 [' E2 ']'
           MOVE 0.86 TO E3 DISPLAY 'I03 [' E3 ']'
           MOVE 8 TO E4 DISPLAY 'I04 [' E4 ']'
      *    a significant digit on the left: written. " 3/05" "*50.86"
           MOVE 3.05 TO E1 DISPLAY 'I05 [' E1 ']'
           MOVE 5.86 TO E3 DISPLAY 'I06 [' E3 ']'
           STOP RUN.
