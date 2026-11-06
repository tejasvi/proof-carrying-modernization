      * OCCURS DEPENDING ON, object outside the group (IBM, OCCURS DEPENDING ON clause): a group
      * containing the table, as a sender, a receiver, a comparison operand, the subject of INSPECT,
      * a STRING source, a DISPLAY operand and with reference modification, has the length of the
      * object's value at the start of the statement; elements above the object keep their storage.
      * Expected: GnuCOBOL (-std=ibm -fno-odoslide) and the model agree on every line.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VODOG.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 N PIC 99 VALUE 5.
       01 G.
          05 H PIC XX VALUE 'AB'.
          05 T OCCURS 1 TO 5 DEPENDING ON N PIC X.
       01 W PIC X(10).
       01 K PIC 99.
       PROCEDURE DIVISION.
           MOVE '1' TO T(1) MOVE '2' TO T(2) MOVE '3' TO T(3)
           MOVE '4' TO T(4) MOVE '5' TO T(5)
           MOVE 3 TO N
           MOVE G TO W
           DISPLAY 'A[' W ']'
           DISPLAY 'B[' G ']'
           MOVE 'XYZWVU' TO G
           MOVE 5 TO N
           DISPLAY 'C[' G ']'
           MOVE 2 TO N
           IF G = 'XY' DISPLAY 'D1' ELSE DISPLAY 'D0' END-IF
           IF G = 'XYZW ' DISPLAY 'F1' ELSE DISPLAY 'F0' END-IF
           MOVE 0 TO K
           INSPECT G TALLYING K FOR ALL 'W'
           DISPLAY 'G' K
           MOVE 4 TO N
           DISPLAY 'I[' G(2:) ']'
           MOVE SPACES TO W
           STRING G '*' DELIMITED BY SIZE INTO W
           DISPLAY 'J[' W ']'
           MOVE 1 TO N
           DISPLAY 'L[' T(3) ']'
           MOVE 'Q' TO T(4)
           MOVE 5 TO N
           DISPLAY 'M[' G ']'
           STOP RUN.
