      * INSPECT forms against GnuCOBOL.  All lines agree except T7,
      * G-lead (GnuCOBOL deviation): LEADING 'A' then CHARACTERS on 20
      * characters starting 'AAB': IBM/standard 2 + 18 (each position
      * is consumed by one phrase), GnuCOBOL 2 + 19.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. INSP1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  S PIC X(20).
       01  C1 PIC 9(4).
       01  C2 PIC 9(4).
       PROCEDURE DIVISION.
           MOVE 'AABACAD  AAB XAAY  ' TO S
           MOVE 0 TO C1 C2
           INSPECT S TALLYING C1 FOR ALL 'A'
           DISPLAY 'T1 ' C1
           MOVE 0 TO C1
           INSPECT S TALLYING C1 FOR LEADING 'A'
           DISPLAY 'T2 ' C1
           MOVE 0 TO C1
           INSPECT S TALLYING C1 FOR CHARACTERS BEFORE INITIAL ' '
           DISPLAY 'T3 ' C1
           MOVE 0 TO C1 C2
           INSPECT S TALLYING C1 FOR ALL 'AA' C2 FOR ALL 'A'
           DISPLAY 'T4 ' C1 ' ' C2
           MOVE 0 TO C1
           INSPECT S TALLYING C1 FOR ALL 'A' AFTER INITIAL 'X'
           DISPLAY 'T5 ' C1
           MOVE 0 TO C1
           INSPECT S TALLYING C1 FOR ALL 'A' BEFORE INITIAL 'X'
               AFTER INITIAL 'C'
           DISPLAY 'T6 ' C1
           MOVE 0 TO C1 C2
           INSPECT S TALLYING C1 FOR LEADING 'A' C2 FOR CHARACTERS
           DISPLAY 'T7 ' C1 ' ' C2
           MOVE 0 TO C1
           INSPECT S TALLYING C1 FOR ALL SPACES
           DISPLAY 'T8 ' C1
           MOVE 0 TO C1 C2
           INSPECT S TALLYING C2 FOR CHARACTERS C1 FOR LEADING 'A'
           DISPLAY 'T9 ' C1 ' ' C2
           INSPECT S REPLACING ALL 'A' BY 'Z'
           DISPLAY 'R1 ' S
           MOVE 'AABACAD  AAB XAAY  ' TO S
           INSPECT S REPLACING LEADING 'A' BY 'L'
           DISPLAY 'R2 ' S
           MOVE 'AABACAD  AAB XAAY  ' TO S
           INSPECT S REPLACING FIRST 'AA' BY 'FF'
           DISPLAY 'R3 ' S
           MOVE 'AABACAD  AAB XAAY  ' TO S
           INSPECT S REPLACING CHARACTERS BY '*' AFTER INITIAL 'X'
           DISPLAY 'R4 ' S
           MOVE 'AABACAD  AAB XAAY  ' TO S
           INSPECT S REPLACING ALL SPACES BY ZERO
           DISPLAY 'R5 ' S
           MOVE 'AABACAD  AAB XAAY  ' TO S
           INSPECT S REPLACING ALL 'A' BY 'B' 'B' BY 'A'
           DISPLAY 'R6 ' S
           MOVE 'AABACAD  AAB XAAY  ' TO S
           INSPECT S CONVERTING 'ABC' TO 'xyz'
           DISPLAY 'C1 ' S
           MOVE 'AABACAD  AAB XAAY  ' TO S
           INSPECT S CONVERTING 'A ' TO '-_' BEFORE INITIAL 'X'
           DISPLAY 'C2 ' S
           MOVE 'AABACAD  AAB XAAY  ' TO S
           MOVE 0 TO C1
           INSPECT S TALLYING C1 FOR ALL 'A' REPLACING ALL 'A' BY 'q'
           DISPLAY 'TR ' C1 ' ' S
           MOVE 'AABACAD  AAB XAAY  ' TO S
           INSPECT S REPLACING ALL 'A' BY 'm' AFTER INITIAL 'B'
               BEFORE INITIAL 'X'
           DISPLAY 'R7 ' S
           MOVE 'XAABACAD  AAB XAAY ' TO S
           INSPECT S REPLACING ALL 'A' BY 'm' BEFORE INITIAL 'X'
               AFTER INITIAL 'B'
           DISPLAY 'R8 ' S
           STOP RUN.
