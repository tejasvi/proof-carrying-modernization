       IDENTIFICATION DIVISION.
       PROGRAM-ID. VCED.
      * MOVE CORRESPONDING into alphanumeric-edited and numeric-edited
      * receivers; a level-66 entry renaming an alphanumeric-edited item.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05  A        PIC X(4) VALUE 'abcd'.
           05  B        PIC 9(4) VALUE 1234.
           05  C        PIC S9(3)V99 VALUE -12.5.
           05  D        PIC X(3) VALUE 'xyz'.
       01  G2.
           05  A        PIC XXBXX.
           05  B        PIC 99/99.
           05  C        PIC -ZZ9.99.
           05  D        PIC X0X0X.
       66  RDX RENAMES D OF G2.
       66  RAB RENAMES A OF G2 THRU B OF G2.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE CORRESPONDING G1 TO G2.
           DISPLAY 'G2=' G2 '.'.
           MOVE 'pqr' TO RDX.
           DISPLAY 'D=' D OF G2 ' RAB=' RAB '.'.
           STOP RUN.
