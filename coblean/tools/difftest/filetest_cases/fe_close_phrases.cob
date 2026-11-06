      * CLOSE ... WITH LOCK and CLOSE / OPEN ... WITH NO REWIND.  IBM: a
      * file closed WITH LOCK cannot be opened again in the run unit
      * (OPEN -> 38); NO REWIND on a non-reel (disk) file gives 07.
      * GnuCOBOL: C1 07, C2 00 (OPEN WITH NO REWIND not implemented), C4
      * 38.  The front end used to drop these phrases; since 10-23 it
      * flags them unsupported (the IR faults at the first one). Since
      * 10-28 CLOSE ... WITH NO REWIND and WITH LOCK are modelled
      * (closetest.py); OPEN ... WITH NO REWIND stays unsupported, so the
      * IR faults at C2.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. RFECLOSE.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT SF ASSIGN TO 'rfeclose.dat'
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD  SF.
       01  S-REC PIC X(6).
       WORKING-STORAGE SECTION.
       01  FS PIC XX.
       PROCEDURE DIVISION.
           OPEN OUTPUT SF
           MOVE 'AAAAAA' TO S-REC
           WRITE S-REC
           CLOSE SF WITH NO REWIND
           DISPLAY 'C1 CLOSE-NO-REWIND ' FS
           OPEN INPUT SF WITH NO REWIND
           DISPLAY 'C2 OPEN-NO-REWIND ' FS
           CLOSE SF WITH LOCK
           DISPLAY 'C3 CLOSE-LOCK ' FS
           OPEN INPUT SF
           DISPLAY 'C4 OPEN-AFTER-LOCK ' FS
           STOP RUN.
