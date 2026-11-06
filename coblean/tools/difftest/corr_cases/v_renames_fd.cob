       IDENTIFICATION DIVISION.
       PROGRAM-ID. VRFD.
      * level-66 entries in a file record (qualified by the record and
      * by the file name), written and read through the file.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO 'CORRF1'
               ORGANIZATION IS SEQUENTIAL.
       DATA DIVISION.
       FILE SECTION.
       FD  F1.
       01  FR.
           05  K1 PIC X(3).
           05  K2.
               10  K21 PIC 9(2).
               10  K22 PIC X(2).
           05  K3 PIC X(4).
       66  RK RENAMES K21 THRU K3.
       66  RN2 RENAMES K21.
       01  FR2.
           05  J1 PIC X(5).
           05  J2 PIC X(6).
       66  RJ RENAMES J2.
       WORKING-STORAGE SECTION.
       01  W PIC X(12).
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           OPEN OUTPUT F1.
           MOVE 'abc' TO K1.
           MOVE '12xyWXYZ' TO RK.
           DISPLAY 'FR=' FR.
           ADD 5 TO RN2 OF FR.
           DISPLAY 'FR=' FR ' RN2=' RN2 OF F1.
           WRITE FR.
           MOVE ALL '-' TO FR.
           MOVE 'pq' TO RJ.
           DISPLAY 'FR2=' FR2.
           WRITE FR2.
           CLOSE F1.
           OPEN INPUT F1.
           READ F1.
           MOVE RK TO W.
           DISPLAY 'W=' W ' RJ=' RJ.
           READ F1.
           DISPLAY 'FR=' FR ' RK=' RK.
           CLOSE F1.
           STOP RUN.
