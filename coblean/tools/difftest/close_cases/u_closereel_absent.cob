      * CLOSE ... REEL of an OPTIONAL file that is not present, opened
      * INPUT (status 05). IBM keeps its "file position indicator and
      * current volume pointer" and gives no status for a file on no
      * medium: the model stops with unsupported at K02. (GnuCOBOL 3.2:
      * 00, and the file is closed: K03 47.)
      * ABSENT: 1
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UCLREELA.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT OPTIONAL F1 ASSIGN TO "uclreela-absent.dat"
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS ST1.
       DATA DIVISION.
       FILE SECTION.
       FD F1.
       01 R1 PIC X(8).
       WORKING-STORAGE SECTION.
       01 ST1 PIC XX VALUE "..".
       PROCEDURE DIVISION.
       M0.
           OPEN INPUT F1
           DISPLAY "K01 " ST1 "|"
           CLOSE F1 REEL
           DISPLAY "K02 REEL " ST1 "|"
           READ F1
           DISPLAY "K03 READ " ST1 "|"
           STOP RUN.
