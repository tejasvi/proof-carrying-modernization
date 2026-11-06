       IDENTIFICATION DIVISION.
       PROGRAM-ID. VNC222A.
      * NC222A's two de-editing tests (MOV-TEST-F2-3, MOV-TEST-F2-4).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  MOVE-TEST-3-A PIC $(4)9.99CR.
       01  MOVE-TEST-3-B PIC S9(4)V99.
       01  MOVE-TEST-4-A PIC --9B.99B99/99.
       01  MOVE-TEST-4-B PIC S99V9(6).
       PROCEDURE DIVISION.
       P0.
           MOVE -123.45 TO MOVE-TEST-3-A
           MOVE MOVE-TEST-3-A TO MOVE-TEST-3-B
           DISPLAY '3A[' MOVE-TEST-3-A ']'
           IF MOVE-TEST-3-B = -123.45
               DISPLAY '3 PASS'
           ELSE
               DISPLAY '3 FAIL'
           END-IF
           MOVE -42.9876 TO MOVE-TEST-4-A
           MOVE MOVE-TEST-4-A TO MOVE-TEST-4-B
           DISPLAY '4A[' MOVE-TEST-4-A ']'
           IF MOVE-TEST-4-B = -42.987600
               DISPLAY '4 PASS'
           ELSE
               DISPLAY '4 FAIL'
           END-IF
           STOP RUN.
