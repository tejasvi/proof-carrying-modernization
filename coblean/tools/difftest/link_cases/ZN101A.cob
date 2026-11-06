       IDENTIFICATION DIVISION.
       PROGRAM-ID. ZN101A.
      * ZN101A calls ZN102A, which calls ZN103A
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  X PIC 9(4) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           CALL "ZN102A" USING X.
           DISPLAY "X=" X.
           STOP RUN.
