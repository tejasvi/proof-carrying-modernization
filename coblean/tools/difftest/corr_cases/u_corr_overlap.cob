       IDENTIFICATION DIVISION.
       PROGRAM-ID. UCOV.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G.
           05  A PIC X(2) VALUE 'aa'.
           05  B PIC X(2) VALUE 'bb'.
       01  H REDEFINES G.
           05  B PIC X(2).
           05  A PIC X(2).
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE CORRESPONDING G TO H.
           DISPLAY 'G=' G.
           STOP RUN.
