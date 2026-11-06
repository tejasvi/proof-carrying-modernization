      * DISPLAY of unsigned numeric literals: the digits as written,
      * without the decimal point (IBM: a numeric literal's decimal
      * point "is treated as an assumed decimal point (that is, as not
      * taking up a character position in the literal)" and its size
      * "is equal to the number of digits specified by the user").
      * IBM's result in each comment (GnuCOBOL 3.2 agrees).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VDISPLIT.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  X1 PIC X(3) VALUE "ABC".
       01  N1 PIC 9(3) VALUE 45.
       PROCEDURE DIVISION.
       P0.
      *    "15" "005" "5" "10000" "007250"
           DISPLAY 'D01 [' 1.5 ']'
           DISPLAY 'D02 [' 0.05 ']'
           DISPLAY 'D03 [' .5 ']'
           DISPLAY 'D04 [' 100.00 ']'
           DISPLAY 'D05 [' 007.250 ']'
      *    integers as before: "15" "007" "0"
           DISPLAY 'D06 [' 15 ']'
           DISPLAY 'D07 [' 007 ']'
           DISPLAY 'D08 [' 0 ']'
      *    "123456789012345678" "123456789" "ABC15030045"
           DISPLAY 'D09 [' 1234567890123456.78 ']'
           DISPLAY 'D10 [' 1234567.89 ']'
           DISPLAY 'D11 [' X1 1.50 30 N1 ']'
           DISPLAY 2.5
           STOP RUN.
