      * EXPECT-REJECT: a CORRESPONDING operand must be a group item
       IDENTIFICATION DIVISION.
       PROGRAM-ID. R13.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  R.
           05  A PIC X(4).
       01  S.
           05  A PIC X(4).
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE CORRESPONDING A OF R TO S.
           STOP RUN.
