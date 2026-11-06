      * EXPECT-FAULT: LOCAL-STORAGE in a called program
      * MODE: sub
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U18.
       DATA DIVISION.
       LOCAL-STORAGE SECTION.
       01  CNT PIC 9(4) VALUE 0.
       LINKAGE SECTION.
       01  N PIC 9(4).
       PROCEDURE DIVISION USING N.
           DISPLAY 'START'.
           ADD 1 TO CNT.
           GOBACK.
