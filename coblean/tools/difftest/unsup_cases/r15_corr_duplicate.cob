      * EXPECT-REJECT: is not unique under
       IDENTIFICATION DIVISION.
       PROGRAM-ID. R15.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05  C PIC X.
           05  C PIC X.
       01  G2.
           05  C PIC X.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE CORRESPONDING G1 TO G2.
           STOP RUN.
