       IDENTIFICATION DIVISION.
       PROGRAM-ID. GREN.
      * G-renusage: a level-66 entry renaming one COMP-3, COMP or COMP-5
      * item. IBM: "All of the data attributes of data-name-2 become the
      * data attributes for data-name-1"; GnuCOBOL 3.2 gives the 66 item
      * DISPLAY storage of the picture's digits (MOVE -5 TO RC writes
      * '005-' over the 2-byte packed C and the next byte).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  DV PIC 9(9)V9(4).
       01  DS PIC X.
       01  R2.
           05  C        PIC S9(3) COMP-3 VALUE -42.
           05  W        PIC S9(4) COMP VALUE -7.
           05  W5       PIC S9(4) COMP-5 VALUE -9.
       66  RC  RENAMES C.
       66  RW  RENAMES W.
       66  RW5 RENAMES W5.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE -5 TO RC.
           MOVE C TO DV.
           IF C < 0 MOVE '-' TO DS ELSE MOVE '+' TO DS END-IF.
           DISPLAY 'C ' DS DV.
           MOVE -6 TO RW.
           MOVE W TO DV.
           IF W < 0 MOVE '-' TO DS ELSE MOVE '+' TO DS END-IF.
           DISPLAY 'W ' DS DV.
           MOVE -8 TO RW5.
           MOVE W5 TO DV.
           IF W5 < 0 MOVE '-' TO DS ELSE MOVE '+' TO DS END-IF.
           DISPLAY 'W5 ' DS DV.
           STOP RUN.
