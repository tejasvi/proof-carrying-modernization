       IDENTIFICATION DIVISION.
       PROGRAM-ID. ALLPRB2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  X4 PIC X(4).
           88 D VALUE ALL "BAC".
           88 E VALUE ALL "B".
           88 F VALUE ALL "Q" "ZZZZ".
       01  G.
           88 GALL VALUE ALL "AB".
           05 G1 PIC X(2).
           05 G2 PIC X(3).
       01  TB.
           05 T PIC X(3) OCCURS 3.
              88 TALL VALUE ALL "Z".
       77  X5 PIC X(5).
           88 H VALUE ALL "xY".
       PROCEDURE DIVISION.
           MOVE "BACB" TO X4.
           IF D DISPLAY "A01 Y|" ELSE DISPLAY "A01 N|" END-IF.
           MOVE "BAC " TO X4.
           IF D DISPLAY "A02 Y|" ELSE DISPLAY "A02 N|" END-IF.
           MOVE "BBBB" TO X4.
           IF E DISPLAY "A03 Y|" ELSE DISPLAY "A03 N|" END-IF.
           IF NOT D DISPLAY "A04 Y|" ELSE DISPLAY "A04 N|" END-IF.
           MOVE "QQQQ" TO X4.
           IF F DISPLAY "A05 Y|" ELSE DISPLAY "A05 N|" END-IF.
           MOVE "ZZZZ" TO X4.
           IF F DISPLAY "A06 Y|" ELSE DISPLAY "A06 N|" END-IF.
           MOVE SPACES TO X4.
           SET D TO TRUE.
           DISPLAY "A07 [" X4 "]|".
           SET E TO TRUE.
           DISPLAY "A08 [" X4 "]|".
           SET F TO TRUE.
           DISPLAY "A09 [" X4 "]|".
           MOVE "ABABA" TO G.
           IF GALL DISPLAY "A10 Y|" ELSE DISPLAY "A10 N|" END-IF.
           MOVE SPACES TO G.
           SET GALL TO TRUE.
           DISPLAY "A11 [" G "]|".
           MOVE "ZZZ" TO T (2).
           IF TALL (2) DISPLAY "A12 Y|" ELSE DISPLAY "A12 N|" END-IF.
           IF TALL (1) DISPLAY "A13 Y|" ELSE DISPLAY "A13 N|" END-IF.
           SET TALL (3) TO TRUE.
           DISPLAY "A14 [" TB "]|".
           SET H TO TRUE.
           DISPLAY "A15 [" X5 "]|".
           IF H DISPLAY "A16 Y|" ELSE DISPLAY "A16 N|" END-IF.
           MOVE "xYxY " TO X5.
           IF H DISPLAY "A17 Y|" ELSE DISPLAY "A17 N|" END-IF.
           IF X5 = ALL "xY" DISPLAY "A18 Y|" ELSE DISPLAY "A18 N|"
           END-IF.
           STOP RUN.
