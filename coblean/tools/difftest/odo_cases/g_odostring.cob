      * G-odostring: STRING ... INTO a group that contains the object of its OCCURS DEPENDING ON table.
      * IBM's maximum length rule lists "STRING ... INTO": the group has its maximum length (6 here),
      * so STRING transfers all 5 characters; GnuCOBOL 3.2 uses the current length (N = 1: 2 bytes).
      * Expected: the lines differ at B: model "B[5PQRSE]" (IBM), GnuCOBOL "B[5PBCDE]".
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GODOSTR.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 R.
          05 N PIC 9.
          05 T OCCURS 0 TO 5 DEPENDING ON N PIC X.
       PROCEDURE DIVISION.
           MOVE 5 TO N
           MOVE '5ABCDE' TO R
           DISPLAY 'A[' R ']'
           MOVE 1 TO N
           STRING '2' 'PQRS' DELIMITED BY SIZE INTO R
           MOVE 5 TO N
           DISPLAY 'B[' R ']'
           STOP RUN.
