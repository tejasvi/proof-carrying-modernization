      * OCCURS DEPENDING ON, object inside the group (IBM: "If the object is in the same group and the
      * group data item is referenced as a receiving item, the maximum length of the group item is
      * used in the operation"; a sending group: the object's value at the start). MOVE of literals,
      * of a group into another such group, of a group with object 0 (OCCURS 0 TO 5).
      * Expected: GnuCOBOL (-std=ibm -fno-odoslide) and the model agree on every line.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VODOM.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 R.
          05 N PIC 9.
          05 T OCCURS 0 TO 5 DEPENDING ON N PIC X.
       01 R2.
          05 N2 PIC 9.
          05 T2 OCCURS 0 TO 5 DEPENDING ON N2 PIC X.
       01 W PIC X(10).
       PROCEDURE DIVISION.
           MOVE 5 TO N
           MOVE '3ABCDE' TO R
           DISPLAY 'A[' R ']'
           MOVE 5 TO N
           DISPLAY 'B[' R ']'
           MOVE 2 TO N
           MOVE 0 TO N2
           MOVE R TO R2
           DISPLAY 'C[' R2 ']'
           MOVE 5 TO N2
           DISPLAY 'D[' R2 ']'
           MOVE 0 TO N
           DISPLAY 'E[' R ']'
           MOVE '4XY' TO R
           DISPLAY 'F[' R ']'
           MOVE 3 TO N
           MOVE SPACES TO W
           MOVE R TO W
           DISPLAY 'H[' W ']'
           STOP RUN.
