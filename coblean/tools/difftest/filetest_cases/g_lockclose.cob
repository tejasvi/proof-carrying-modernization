      * G-lockclose (GnuCOBOL): CLOSE of a file that was closed WITH
      * LOCK.  IBM: 42 (the file is not open).  GnuCOBOL: 00 for a
      * sequential file (L2) and a crash (SIGSEGV, 'attempt to reference
      * invalid memory address') for an indexed file (M2).  Until 10-28
      * the model had no WITH LOCK: the front end flagged it unsupported
      * (the IR faulted at L1). Since then L2 and M2 give 42 (and the
      * file stays locked): close_cases/g_lockclose_seq.cob and
      * g_lockclose_idx.cob, closetest.py.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. RLOCKCL.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT SF ASSIGN TO 'rlockcl1.dat'
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS FS1.
           SELECT KF ASSIGN TO 'rlockcl2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS K-KEY
               FILE STATUS IS FS2.
       DATA DIVISION.
       FILE SECTION.
       FD  SF.
       01  S-REC PIC X(6).
       FD  KF.
       01  K-REC.
           05  K-KEY   PIC X(3).
           05  K-DATA  PIC X(3).
       WORKING-STORAGE SECTION.
       01  FS1 PIC XX.
       01  FS2 PIC XX.
       PROCEDURE DIVISION.
           OPEN OUTPUT SF
           CLOSE SF WITH LOCK
           DISPLAY 'L1 CLOSE-LOCK ' FS1
           CLOSE SF
           DISPLAY 'L2 CLOSE-AGAIN ' FS1
           OPEN OUTPUT KF
           CLOSE KF WITH LOCK
           DISPLAY 'M1 CLOSE-LOCK ' FS2
           CLOSE KF
           DISPLAY 'M2 CLOSE-AGAIN ' FS2
           STOP RUN.
