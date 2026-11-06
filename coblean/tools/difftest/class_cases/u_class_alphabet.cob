      * Unsupported statement: a class condition with a class name in a
      * program collating sequence given by literals (the expansion's
      * comparisons would be collated).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UCALPH.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       OBJECT-COMPUTER. X
           PROGRAM COLLATING SEQUENCE IS SEQ1.
       SPECIAL-NAMES.
           ALPHABET SEQ1 IS 'B' ALSO 'A' 'C'
           CLASS CB IS 'B'.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 A1 PIC X VALUE 'A'.
       PROCEDURE DIVISION.
           IF A1 CB DISPLAY 'Q01 Y|' ELSE DISPLAY 'Q01 N|' END-IF
           STOP RUN.
