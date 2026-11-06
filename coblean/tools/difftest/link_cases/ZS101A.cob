       IDENTIFICATION DIVISION.
       PROGRAM-ID. ZS101A.
      * caller and callee both have sections MAIN-S and WORK-S
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  X PIC 9(4) VALUE 0.
       PROCEDURE DIVISION.
       MAIN-S SECTION.
       P0.
           CALL "ZS102A" USING X.
           DISPLAY "AFTER CALL X=" X.
           PERFORM WORK-S.
           DISPLAY "X=" X.
           STOP RUN.
       WORK-S SECTION.
       W1.
           ADD 10 TO X.
