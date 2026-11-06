      * WRITE ... FROM and READ ... INTO with a group that contains its object (NIST SQ214A's
      * pattern): WRITE FROM sends the group's current length; READ INTO is one of the statements
      * of IBM's maximum length rule, so the receiving group gets the record read up to its maximum
      * length and its object comes from the record.
      * Expected: GnuCOBOL (-std=ibm -fno-odoslide) and the model agree on every line.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VODOF2.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F ASSIGN TO 'VODOF2DT' ORGANIZATION SEQUENTIAL
               FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD F.
       01 FR PIC X(12).
       WORKING-STORAGE SECTION.
       01 FS PIC XX.
       01 R.
          05 N PIC 9.
          05 H PIC XX.
          05 T OCCURS 1 TO 9 DEPENDING ON N PIC X.
       PROCEDURE DIVISION.
           OPEN OUTPUT F
           MOVE 9 TO N
           MOVE '3AB123456789' TO R
           WRITE FR FROM R
           DISPLAY 'W1 ' FS ' [' FR ']'
           MOVE 9 TO N
           MOVE '7CD12345678' TO R
           WRITE FR FROM R
           DISPLAY 'W2 ' FS ' [' FR ']'
           CLOSE F
           OPEN INPUT F
           MOVE 9 TO N
           MOVE SPACES TO R
           MOVE 5 TO N
           READ F INTO R
           DISPLAY 'R1 ' FS ' [' R ']'
           MOVE 9 TO N
           DISPLAY 'R2 [' R ']'
           READ F INTO R
           DISPLAY 'R3 ' FS ' [' R ']'
           CLOSE F
           STOP RUN.
