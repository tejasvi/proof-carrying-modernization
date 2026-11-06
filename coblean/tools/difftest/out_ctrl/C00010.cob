       IDENTIFICATION DIVISION.
       PROGRAM-ID. C00010.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 R.
          05 TRC PIC X(80) VALUE SPACES.
          05 TLEN PIC 9(3) COMP VALUE 0.
          05 STEPS PIC 9(3) COMP VALUE 0.
          05 K PIC 9(3) COMP VALUE 1.
          05 J PIC 9(3) COMP VALUE 0.
          05 FLAG PIC X VALUE 'N'.
       01 RX REDEFINES R.
          05 BYTE PIC X OCCURS 89.
       01 IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN SECTION.
       MAIN-DRIVER.
           PERFORM P0 THRU P4
           PERFORM DUMP
           STOP RUN.
       S0 SECTION.
       P0.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'A' TO TRC(TLEN:1)
           PERFORM P4
           PERFORM S1
           .
       S1 SECTION.
       P1.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'B' TO TRC(TLEN:1)
           GO TO P2 P3 P4 DEPENDING ON K
           IF STEPS < 49
           GO TO P1
           END-IF
           .
       S2 SECTION.
       P2.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'C' TO TRC(TLEN:1)
           IF STEPS > 10
           EXIT PARAGRAPH
           END-IF
           PERFORM P4
           .
           .
       P3.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'D' TO TRC(TLEN:1)
           ADD 1 TO J
           PERFORM P4
           .
           PERFORM P4
           .
       P4.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'E' TO TRC(TLEN:1)
           IF STEPS < 21
           GO TO P1
           END-IF
           .
           ADD 1 TO J
           .
       DUMPS SECTION.
       DUMP.
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 89
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '.
       STOPPER.
           PERFORM DUMP
           STOP RUN.
