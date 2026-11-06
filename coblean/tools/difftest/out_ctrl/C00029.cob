       IDENTIFICATION DIVISION.
       PROGRAM-ID. C00029.
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
           PERFORM P0 THRU P6
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
           PERFORM P2 THRU P4 1 TIMES
           .
       P1.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'B' TO TRC(TLEN:1)
           PERFORM S2
           IF STEPS < 28
           GO TO P5
           END-IF
           PERFORM VARYING K FROM 1 BY 1 UNTIL K > 3
           ADD 1 TO J
           END-PERFORM
           .
       S1 SECTION.
       P2.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'C' TO TRC(TLEN:1)
           PERFORM VARYING K FROM 1 BY 1 UNTIL K > 2
           IF STEPS < 36
           GO TO P5
           END-IF
           END-PERFORM
           ADD 1 TO J
           GO TO P3 P6 P4 DEPENDING ON K
           .
       P3.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'D' TO TRC(TLEN:1)
           PERFORM S2
           PERFORM S2
           PERFORM VARYING K FROM 1 BY 1 UNTIL K > 3
           PERFORM P5 THRU P6
           END-PERFORM
           .
           .
       S2 SECTION.
       P4.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'E' TO TRC(TLEN:1)
           PERFORM P5 THRU P6
           .
       P5.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'F' TO TRC(TLEN:1)
           PERFORM P6
           .
       P6.
           ADD 1 TO STEPS
           IF STEPS > 60
           GO TO STOPPER
           END-IF
           ADD 1 TO TLEN
           MOVE 'G' TO TRC(TLEN:1)
           IF STEPS > 10
           EXIT PARAGRAPH
           END-IF
           ADD 1 TO J
           IF STEPS < 18
           GO TO P5
           END-IF
           GO TO STOPPER
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
