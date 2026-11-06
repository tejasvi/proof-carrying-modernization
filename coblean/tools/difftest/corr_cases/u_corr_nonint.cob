       IDENTIFICATION DIVISION.
       PROGRAM-ID. P1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05  A        PIC X(3) VALUE 'a1a'.
           05  B        PIC 9(3) VALUE 123.
           05  C.
               10  D    PIC X(2) VALUE 'd1'.
               10  E    PIC 9(2) VALUE 45.
           05  FILLER.
               10  F    PIC X(2) VALUE 'f1'.
           05  H        PIC X(2) VALUE 'h1'.
           05  HR REDEFINES H PIC X(2).
           05  T        OCCURS 2 PIC X VALUE 't'.
           05  K.
               10  KA   PIC X VALUE 'k'.
           05  M        PIC X(4) VALUE 'mmmm'.
           05  N        PIC 9(2)V9 VALUE 12.5.
           05  Q.
               10 QA    PIC X VALUE 'q'.
               10 QB    PIC X VALUE 'r'.
       01  G2.
           05  Q.
               10 QB    PIC X VALUE '-'.
               10 QA    PIC X VALUE '-'.
           05  N        PIC X(4) VALUE '----'.
           05  M.
               10 M1    PIC X(2) VALUE '--'.
               10 M2    PIC X(2) VALUE '--'.
           05  K        PIC X(2) VALUE '--'.
           05  T        OCCURS 2 PIC X VALUE '-'.
           05  HR       PIC X(2) VALUE '--'.
           05  H        PIC X(2) VALUE '--'.
           05  FILLER.
               10  F    PIC X(2) VALUE '--'.
           05  C.
               10  E    PIC 9(2) VALUE 0.
               10  X    PIC X VALUE '-'.
               10  D    PIC X(2) VALUE '--'.
           05  B        PIC X(3) VALUE '---'.
           05  A        PIC X(3) VALUE '---'.
       PROCEDURE DIVISION.
       P0.
           MOVE CORRESPONDING G1 TO G2.
           DISPLAY 'G2=' G2 '.'.
           STOP RUN.
