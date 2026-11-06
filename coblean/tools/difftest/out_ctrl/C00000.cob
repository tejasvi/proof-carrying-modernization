       IDENTIFICATION DIVISION.
       PROGRAM-ID. C00000.
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
       MAIN-DRIVER.
           PERFORM P0 THRU P5
           PERFORM DUMP
           STOP RUN.
       P0.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'A' TO TRC(TLEN:1)
           ADD 1 TO J
           IF STEPS > 10
           EXIT PARAGRAPH
           END-IF
           GO TO P4 P3 P0 DEPENDING ON K
           .
       P1.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'B' TO TRC(TLEN:1)
           ADD 1 TO J
           .
           IF STEPS < 30
           GO TO P5
           END-IF
           .
       P2.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'C' TO TRC(TLEN:1)
           PERFORM P5 0 TIMES
           .
       P3.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'D' TO TRC(TLEN:1)
           IF STEPS > 10
           EXIT PARAGRAPH
           END-IF
           ADD 1 TO J
           PERFORM P5
           .
       P4.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'E' TO TRC(TLEN:1)
           PERFORM P5
           .
       P5.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'F' TO TRC(TLEN:1)
           IF STEPS < 60
           GO TO P0
           END-IF
           IF STEPS < 13
           GO TO P5
           END-IF
           .
       DUMP.
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 89
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '.
       STOPPER.
           PERFORM DUMP
           STOP RUN.
