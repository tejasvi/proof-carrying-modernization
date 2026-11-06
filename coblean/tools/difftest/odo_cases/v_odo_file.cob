      * A record with an OCCURS DEPENDING ON table and no RECORD clause makes the file variable-length
      * (IBM, RECORD clause format 3: "If data-name-1 is not specified and the record contains a
      * variable occurrence data item", the fixed part and the current occurrences are written).
      * Expected: GnuCOBOL (-std=ibm -fno-odoslide) and the model agree on every line.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VODOF.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F ASSIGN TO 'VODOFDAT' ORGANIZATION SEQUENTIAL
               FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD F.
       01 FR.
          05 FN PIC 9.
          05 FT OCCURS 1 TO 5 DEPENDING ON FN PIC X.
       WORKING-STORAGE SECTION.
       01 FS PIC XX.
       01 W PIC X(8).
       PROCEDURE DIVISION.
           OPEN OUTPUT F
           MOVE 5 TO FN
           MOVE '3ABCDE' TO FR
           WRITE FR
           DISPLAY 'W1 ' FS
           MOVE '5VWXYZ' TO FR
           WRITE FR
           DISPLAY 'W2 ' FS
           MOVE 1 TO FN
           MOVE 'Q' TO FT(1)
           WRITE FR
           DISPLAY 'W3 ' FS
           CLOSE F
           OPEN INPUT F
           PERFORM 4 TIMES
              MOVE ALL '#' TO W
              READ F INTO W
              DISPLAY 'R ' FS ' [' W '] [' FR ']'
           END-PERFORM
           CLOSE F
           STOP RUN.
