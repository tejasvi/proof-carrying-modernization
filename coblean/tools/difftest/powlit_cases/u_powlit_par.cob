       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWLP.
      * ar2-fix hand case: a COMP-5 base can hold more digits than its
      * PICTURE, so C5 ** 3 has 30 to 60 digits: whether IBM carries it
      * exactly or with dmax places is open; unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  C5       PIC S9(5)V9(5) COMP-5 VALUE 1.5.
       01  D5       PIC S9(2) COMP-5 VALUE 12.
       01  R9       PIC 9(9)V9(9) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE R9 = D5 ** 3
           DISPLAY "V01 " R9
           COMPUTE R9 = C5 ** 3
           DISPLAY "U01 " R9
           STOP RUN.
