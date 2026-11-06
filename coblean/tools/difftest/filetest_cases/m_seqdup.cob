      * ACCESS SEQUENTIAL WRITE.  A3: K01 again after K02 (lower than
      * the previous key, and in the file): IBM 21 (keys must ascend;
      * VSAM's sequential insert compares with the previous key first);
      * both sides 21 (model fixed 10-23).  A4: K02 again (equal to the
      * previous key): model 22 (duplicate), GnuCOBOL 21 (G-dup21: every
      * duplicate in OUTPUT mode is 21).  A6: alternate key A1 in use,
      * record key ascending: IBM 22 (duplicate alternate key without
      * DUPLICATES), model 22, GnuCOBOL 21.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. RSEQDUP.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT KF ASSIGN TO 'rseqdup.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS K-KEY
               ALTERNATE RECORD KEY IS K-ALT
               FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD  KF.
       01  K-REC.
           05  K-KEY   PIC X(3).
           05  K-ALT   PIC X(2).
           05  K-DATA  PIC X(3).
       WORKING-STORAGE SECTION.
       01  FS PIC XX.
       PROCEDURE DIVISION.
           OPEN OUTPUT KF
           MOVE 'K01A1D01' TO K-REC
           WRITE K-REC
           DISPLAY 'A1 K01 ' FS
           MOVE 'K02A2D02' TO K-REC
           WRITE K-REC
           DISPLAY 'A2 K02 ' FS
           MOVE 'K01A3D03' TO K-REC
           WRITE K-REC
           DISPLAY 'A3 K01-AGAIN ' FS
           MOVE 'K02A4D04' TO K-REC
           WRITE K-REC
           DISPLAY 'A4 K02-AGAIN ' FS
           MOVE 'K03A5D05' TO K-REC
           WRITE K-REC
           DISPLAY 'A5 K03 ' FS
           MOVE 'K04A1D06' TO K-REC
           WRITE K-REC
           DISPLAY 'A6 K04-ALT-A1 ' FS
           CLOSE KF
           STOP RUN.
