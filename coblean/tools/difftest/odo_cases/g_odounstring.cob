      * G-odounstring: UNSTRING ... INTO a group that contains the object of its OCCURS DEPENDING ON
      * table. IBM's maximum length rule lists "UNSTRING ... INTO": the receiving group has its
      * maximum length (6), so it gets all of "3KLMNO"; GnuCOBOL 3.2 uses the current length (N = 1).
      * Expected: the lines differ at B: model "B[5KLMNO]" (IBM), GnuCOBOL "B[5KBCDE]".
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GODOUNS.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 R.
          05 N PIC 9.
          05 T OCCURS 0 TO 5 DEPENDING ON N PIC X.
       01 S PIC X(6) VALUE '3KLMNO'.
       PROCEDURE DIVISION.
           MOVE 5 TO N
           MOVE '5ABCDE' TO R
           DISPLAY 'A[' R ']'
           MOVE 1 TO N
           UNSTRING S INTO R
           MOVE 5 TO N
           DISPLAY 'B[' R ']'
           STOP RUN.
