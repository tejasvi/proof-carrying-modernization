      * G-parencomma: separator commas inside parentheses (IBM: each is
      * a space for matching; cobc 3.2 keeps them). Expected: L01, L02
      * differ (model q p, GnuCOBOL r s); L03 agrees (p).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GPARENCOMMA.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 W-C PIC X VALUE SPACE.
       01 TT VALUE 'pqrs'.
          05 TR OCCURS 2.
             10 T PIC X OCCURS 2.
       PROCEDURE DIVISION.
           COPY CRPAREN REPLACING ==T (2 1)== BY ==T (1 2)==
                                  ==(2 2)== BY ==(1 1)==.
           STOP RUN.
