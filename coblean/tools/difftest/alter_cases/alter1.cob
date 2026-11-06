       IDENTIFICATION DIVISION.
       PROGRAM-ID. ALTER1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9(2) VALUE 0.
       01  T PIC X(20) VALUE SPACES.
       PROCEDURE DIVISION.
       MAIN-PARA.
           PERFORM DISPATCH THRU DISPATCH-EXIT.
           ALTER SWITCH TO PROCEED TO P-B.
           PERFORM DISPATCH THRU DISPATCH-EXIT.
           ALTER SWITCH TO PROCEED TO P-C.
           PERFORM DISPATCH THRU DISPATCH-EXIT.
           ALTER SWITCH TO PROCEED TO P-A.
           PERFORM DISPATCH THRU DISPATCH-EXIT.
           ALTER SWITCH TO P-B.
           GO TO SWITCH.
       AFTER-B.
           DISPLAY 'AFTER ' T ' ' N.
           STOP RUN.
       DISPATCH.
           ADD 1 TO N.
       SWITCH.
           GO TO P-A.
       P-A.
           MOVE 'A' TO T
           DISPLAY 'IN A ' N
           GO TO DISPATCH-EXIT.
       P-B.
           MOVE 'B' TO T
           DISPLAY 'IN B ' N
           IF N > 4
              GO TO AFTER-B
           END-IF
           GO TO DISPATCH-EXIT.
       P-C.
           MOVE 'C' TO T
           DISPLAY 'IN C ' N.
       DISPATCH-EXIT.
           EXIT.
