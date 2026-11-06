       IDENTIFICATION DIVISION.
       PROGRAM-ID. ZS102A.
       DATA DIVISION.
       LINKAGE SECTION.
       01  Y PIC 9(4).
       PROCEDURE DIVISION USING Y.
       MAIN-S SECTION.
       P1.
           PERFORM WORK-S.
           GOBACK.
       WORK-S SECTION.
       W1.
           ADD 1 TO Y.
       W2.
           ADD 2 TO Y.
