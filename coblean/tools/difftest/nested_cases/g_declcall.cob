      * G-declcall (GnuCOBOL 3.2): after the USE GLOBAL declarative of the main program has run
      * for the READ of the contained program Q9N, the second CALL of the separately compiled
      * program Q9B0 crashes GnuCOBOL (SIGSEGV, "libcob: ", hang). IBM and the model: START Q9B0
      * DA 01 Q9N END BACK N Q9B0 BACK B0.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q9.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT TF ASSIGN TO 'GDCTF.DAT'
               ORGANIZATION IS SEQUENTIAL.
       DATA DIVISION.
       FILE SECTION.
       FD TF GLOBAL.
       01 TR PIC X(8).
       WORKING-STORAGE SECTION.
       01 D GLOBAL PIC 99 VALUE 0.
       PROCEDURE DIVISION.
       DECLARATIVES.
       DA SECTION.
           USE GLOBAL AFTER ERROR PROCEDURE ON INPUT.
       DA1.
           ADD 1 TO D.
           DISPLAY 'DA ' D.
       END DECLARATIVES.
       MAIN SECTION.
       M1.
           DISPLAY 'START'.
           OPEN OUTPUT TF.
           CLOSE TF.
           CALL 'Q9B0'.
           CALL 'Q9N'.
           DISPLAY 'BACK N'.
           CALL 'Q9B0'.
           DISPLAY 'BACK B0'.
           STOP RUN.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q9N.
       PROCEDURE DIVISION.
           OPEN INPUT TF.
           READ TF.
           CLOSE TF.
           DISPLAY 'Q9N END'.
           EXIT PROGRAM.
       END PROGRAM Q9N.
       END PROGRAM Q9.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q9B1.
       PROCEDURE DIVISION.
           DISPLAY 'Q9B1'.
           CALL 'Q9B0'.
           EXIT PROGRAM.
       END PROGRAM Q9B1.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q9B0.
       PROCEDURE DIVISION.
           DISPLAY 'Q9B0'.
           EXIT PROGRAM.
       END PROGRAM Q9B0.
