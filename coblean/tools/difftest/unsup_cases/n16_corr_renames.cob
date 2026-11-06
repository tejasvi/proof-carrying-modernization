      * EXPECT-RUN
       IDENTIFICATION DIVISION.
       PROGRAM-ID. N11.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05  A PIC X(2) VALUE 'aa'.
           05  N PIC 9(3) VALUE 5.
       01  G2.
           05  N PIC 9(3) VALUE 7.
           05  A PIC X(2) VALUE '--'.
       66  RA RENAMES N OF G2 THRU A OF G2.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE CORRESPONDING G1 TO G2.
           ADD CORRESPONDING G1 TO G2 ON SIZE ERROR DISPLAY 'E'.
           SUBTRACT CORR G1 FROM G2.
           DISPLAY RA.
           STOP RUN.
