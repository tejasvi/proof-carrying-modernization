      * OPEN of a file closed WITH LOCK (38, IBM: "An OPEN statement was
      * attempted on a file previously closed with lock") runs the USE
      * AFTER STANDARD EXCEPTION declarative of the file, as NIST SQ215A
      * tests; the declarative of the indexed file sees 38 too. Every
      * line agrees with GnuCOBOL 3.2.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VCLLOCK2.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO "vcllock2-f1.dat"
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS ST1.
           SELECT F3 ASSIGN TO "vcllock2-f3.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS K3
               FILE STATUS IS ST3.
       DATA DIVISION.
       FILE SECTION.
       FD F1.
       01 R1 PIC X(8).
       FD F3.
       01 R3.
          05 K3 PIC X(3).
          05 V3 PIC X(5).
       WORKING-STORAGE SECTION.
       01 ST1 PIC XX VALUE "..".
       01 ST3 PIC XX VALUE "..".
       01 NDECL PIC 9 VALUE 0.
       PROCEDURE DIVISION.
       DECLARATIVES.
       D1 SECTION.
           USE AFTER STANDARD EXCEPTION PROCEDURE ON F1.
       D1P.
           ADD 1 TO NDECL
           DISPLAY "D1 " ST1 " " NDECL "|".
       D3 SECTION.
           USE AFTER STANDARD ERROR PROCEDURE ON F3.
       D3P.
           ADD 1 TO NDECL
           DISPLAY "D3 " ST3 " " NDECL "|".
       END DECLARATIVES.
       M SECTION.
       M0.
           OPEN OUTPUT F1 F3
           DISPLAY "A01 " ST1 " " ST3 "|"
           CLOSE F1 WITH LOCK
           DISPLAY "A02 LOCK " ST1 "|"
           OPEN OUTPUT F1
           DISPLAY "A03 " ST1 " " NDECL "|"
           OPEN INPUT F1
           DISPLAY "A04 " ST1 " " NDECL "|"
           CLOSE F3 WITH LOCK
           DISPLAY "A05 LOCK " ST3 "|"
           OPEN I-O F3
           DISPLAY "A06 " ST3 " " NDECL "|"
           STOP RUN.
