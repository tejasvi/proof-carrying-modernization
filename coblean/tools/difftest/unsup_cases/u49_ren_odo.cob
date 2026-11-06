      * EXPECT-FAULT: RENAMES of the group G with an OCCURS DEPENDING ON table
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U47.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9 VALUE 2.
       01  R.
           05  A PIC X(4).
           05  G.
               10  T PIC X OCCURS 1 TO 5 DEPENDING ON N.
       66  RG RENAMES G.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
