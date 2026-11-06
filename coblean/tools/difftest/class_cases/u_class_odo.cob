      * Unsupported statement: a class condition with a class name on a
      * group containing an OCCURS DEPENDING ON table (variable length).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UCODO.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           CLASS DIG IS '0' THRU '9'.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 K PIC 9 VALUE 2.
       01 G.
          05 T PIC X OCCURS 1 TO 4 DEPENDING ON K.
       PROCEDURE DIVISION.
           MOVE '12' TO G
           IF G DIG DISPLAY 'Q01 Y|' ELSE DISPLAY 'Q01 N|' END-IF
           STOP RUN.
