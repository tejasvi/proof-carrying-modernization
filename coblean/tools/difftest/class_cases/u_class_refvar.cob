      * Unsupported statement: a class condition with a class name on a
      * reference modification whose length is a data name.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UCREF.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           CLASS DIG IS '0' THRU '9'.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 A1 PIC X(4) VALUE '12AB'.
       01 L PIC 9 VALUE 2.
       PROCEDURE DIVISION.
           IF A1(1:L) DIG DISPLAY 'Q01 Y|' ELSE DISPLAY 'Q01 N|' END-IF
           STOP RUN.
