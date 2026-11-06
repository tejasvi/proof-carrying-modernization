      * Plain INITIALIZE and INITIALIZE ... REPLACING leave a USAGE
      * POINTER item unchanged (IBM rule 1a: not a MOVE receiver).
      * Expected (initptr_checks.sh): P KEPT, X [ ], P KEPT, X [Z]. Model
      * only (GnuCOBOL's pointer has 8 bytes, the model's 4).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. PTR1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G.
           05 P POINTER.
           05 X PIC X.
       01  GX REDEFINES G PIC X(5).
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE 'ABCDE' TO GX
           INITIALIZE G
           IF GX (1:4) = LOW-VALUES DISPLAY 'P ZEROED'
           ELSE DISPLAY 'P KEPT' END-IF
           DISPLAY 'X [' X ']'
           MOVE 'ABCDE' TO GX
           INITIALIZE G REPLACING NUMERIC BY 0 ALPHANUMERIC BY 'Z'
           IF GX (1:4) = LOW-VALUES DISPLAY 'P ZEROED'
           ELSE DISPLAY 'P KEPT' END-IF
           DISPLAY 'X [' X ']'
           STOP RUN.
