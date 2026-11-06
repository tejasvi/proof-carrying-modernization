      * G-ins0 (GnuCOBOL 3.2 departs from IBM): the simple insertion
      * symbols 0 and / in or right after a floating insertion string
      * or a zero-suppression string. IBM: "Any simple-insertion symbols
      * (B 0 / ,) within or to the immediate right of the string of
      * floating insertion symbols are considered part of the floating
      * character-string" (zero suppression likewise). GnuCOBOL writes
      * 0 and / there (G01 G02 G03 G05 G10); B and , agree.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GINS0.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 E1 PIC +0+.
       01 E2 PIC ++++09.9.
       01 E3 PIC --0--999.9.
       01 E4 PIC +B+9.
       01 E5 PIC $/$$9.
       01 E6 PIC $$,$$9.
       01 E7 PIC ++B++9.
       01 E8 PIC $ZZ09.999.
       PROCEDURE DIVISION.
           MOVE 6 TO E1 DISPLAY "G01 [" E1 "]|"
           MOVE ZERO TO E2 DISPLAY "G02 [" E2 "]|"
           MOVE 78244.1 TO E3 DISPLAY "G03 [" E3 "]|"
           MOVE 5 TO E4 DISPLAY "G04 [" E4 "]|"
           MOVE 12 TO E5 DISPLAY "G05 [" E5 "]|"
           MOVE 123 TO E6 DISPLAY "G06 [" E6 "]|"
           MOVE 12 TO E7 DISPLAY "G07 [" E7 "]|"
           MOVE 1234 TO E7 DISPLAY "G08 [" E7 "]|"
           MOVE 0 TO E6 DISPLAY "G09 [" E6 "]|"
           MOVE 0 TO E8 DISPLAY "G10 [" E8 "]|"
           STOP RUN.
