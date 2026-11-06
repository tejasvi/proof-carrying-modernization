      * Unsupported statement: a class condition with a class name on a
      * binary item (IBM: identifier-1 must be USAGE DISPLAY).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UCUSE.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           CLASS DIG IS '0' THRU '9'.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 C1 PIC 9(4) COMP VALUE 12.
       PROCEDURE DIVISION.
           IF C1 DIG DISPLAY 'Q01 Y|' ELSE DISPLAY 'Q01 N|' END-IF
           STOP RUN.
