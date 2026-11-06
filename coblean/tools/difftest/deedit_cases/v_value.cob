       IDENTIFICATION DIVISION.
       PROGRAM-ID. VVALUE.
      * Edited values set by VALUE (no editing): they de-edit.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E1 PIC ZZ9.99 VALUE '  1.50'.
       01  E2 PIC ZZ9.99 BLANK WHEN ZERO VALUE SPACES.
       01  E3 PIC ***9.99- VALUE '***5.25-'.
       01  N1 PIC S9(4)V99.
       01  N1X REDEFINES N1 PIC X(6).
       PROCEDURE DIVISION.
       P0.
           MOVE E1 TO N1 DISPLAY 'E1 N1[' N1X ']'
           MOVE E2 TO N1 DISPLAY 'E2 N1[' N1X ']'
           MOVE E3 TO N1 DISPLAY 'E3 N1[' N1X ']'
           STOP RUN.
