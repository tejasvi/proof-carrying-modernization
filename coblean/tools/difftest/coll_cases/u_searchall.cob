      * SEARCH ALL with an alphanumeric KEY in a program with a PROGRAM
      * COLLATING SEQUENCE: the model's KEY-order check compares in
      * native order, so the statement is unsupported (the model stops
      * there; GnuCOBOL runs it). The line before it agrees.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. USALL.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       OBJECT-COMPUTER. X
           PROGRAM COLLATING SEQUENCE IS SEQ1.
       SPECIAL-NAMES.
           ALPHABET SEQ1 IS "ZYX".
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 T1 VALUE "ZYXAB".
          05 TE OCCURS 5 ASCENDING KEY TK INDEXED BY TX.
             10 TK PIC X.
       PROCEDURE DIVISION.
           DISPLAY "START".
           SEARCH ALL TE AT END DISPLAY "END"
              WHEN TK(TX) = "X" DISPLAY "FOUND".
           STOP RUN.
