      * COBC: -std=ibm
      * G-odoslide: with -std=ibm (odoslide: yes) GnuCOBOL 3.2 drops IBM's maximum length rule: a MOVE
      * into a group that contains its object fills the group's current length (N = 0: 1 byte), and a
      * reference modification without a length uses the maximum length. IBM (and GnuCOBOL with
      * -fno-odoslide, which odotest.py uses): the maximum length, and the current length.
      * Expected: the lines differ at A, B and C: model "A[4XY  ]" "B[5XY   ]" "C[XY ]",
      * GnuCOBOL "A[4ABCD]" "B[5ABCDE]" "C[ABCD]".
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GODOSLD.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 R.
          05 N PIC 9.
          05 T OCCURS 0 TO 5 DEPENDING ON N PIC X.
       PROCEDURE DIVISION.
           MOVE 5 TO N
           MOVE '5ABCDE' TO R
           MOVE 0 TO N
           MOVE '4XY' TO R
           DISPLAY 'A[' R ']'
           MOVE 5 TO N
           DISPLAY 'B[' R ']'
           MOVE 3 TO N
           DISPLAY 'C[' R(2:) ']'
           STOP RUN.
