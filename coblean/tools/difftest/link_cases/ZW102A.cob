       IDENTIFICATION DIVISION.
       PROGRAM-ID. ZW102A.
       DATA DIVISION.
       LINKAGE SECTION.
       01  Y PIC 9(4).
       PROCEDURE DIVISION USING Y.
       P1.
           ADD 1 TO Y.
       P2.
           EXIT PROGRAM.
       P3.
           ADD 100 TO Y.
           GO TO P2.
