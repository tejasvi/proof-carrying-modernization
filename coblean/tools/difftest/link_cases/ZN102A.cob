       IDENTIFICATION DIVISION.
       PROGRAM-ID. ZN102A.
       DATA DIVISION.
       LINKAGE SECTION.
       01  Y PIC 9(4).
       PROCEDURE DIVISION USING Y.
       P1.
           ADD 1 TO Y.
           CALL "ZN103A" USING Y.
           DISPLAY "IN ZN102A Y=" Y.
           ADD 100 TO Y.
           EXIT PROGRAM.
       P2.
           ADD 1000 TO Y.
