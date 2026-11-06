      * Plain INITIALIZE of identifiers with pointers among their rule-1
      * candidates (G1: a pointer, a table of pointers, an AE item; G2: a
      * pointer in a group whose sibling redefines it) is lowered to MOVEs
      * that skip the pointers; G3 (its pointer only under a REDEFINES
      * child) goes to the resolver. Then REPLACING on G1, and INITIALIZE
      * of a pointer, a named unsupported statement. Expected lines and
      * end: initptr_checks.sh. Model only (pointer sizes differ).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. PTR2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05 G1P POINTER.
           05 G1A PIC X(3).
           05 G1E PIC XX/X.
           05 G1N PIC 9(2).
           05 G1T OCCURS 2.
              10 G1TP POINTER.
              10 G1TX PIC X.
       01  G1X REDEFINES G1 PIC X(23).
       01  G2.
           05 G2A PIC X(2).
           05 G2E PIC X0X.
           05 G2R.
              10 G2RP POINTER.
           05 G2S REDEFINES G2R.
              10 G2SX PIC X(4).
       01  G2X REDEFINES G2 PIC X(9).
       01  G3.
           05 G3A PIC X(2).
           05 G3B PIC X(4).
           05 G3C REDEFINES G3B.
              10 G3CP POINTER.
       01  G3X REDEFINES G3 PIC X(6).
       01  P3 POINTER.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE ALL '#' TO G1X G2X G3X
           INITIALIZE G2 G1 G3
           DISPLAY 'G1 [' G1X ']'
           DISPLAY 'G2 [' G2X ']'
           DISPLAY 'G3 [' G3X ']'
           MOVE ALL '#' TO G1X
           INITIALIZE G1 REPLACING ALPHANUMERIC BY 'Q' NUMERIC BY 7
           DISPLAY 'G1 [' G1X ']'
           INITIALIZE P3
           DISPLAY 'NOT REACHED'
           STOP RUN.
