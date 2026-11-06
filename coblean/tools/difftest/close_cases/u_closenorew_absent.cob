      * CLOSE ... WITH NO REWIND of an OPTIONAL file that is not present,
      * opened INPUT (status 05). IBM gives no status for a file on no
      * medium: the model stops with unsupported at N02. (GnuCOBOL 3.2:
      * 00, N02.)
      * ABSENT: 1
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UCLNORWA.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT OPTIONAL F1 ASSIGN TO "uclnorwa-absent.dat"
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
           DISPLAY "N01 " ST1 "|"
           CLOSE F1 WITH NO REWIND
           DISPLAY "N02 NO REWIND " ST1 "|"
           STOP RUN.
