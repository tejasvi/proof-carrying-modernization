      * M-43 (model, fixed 10-23 by Sem.clearCur): an unsuccessful I/O
      * statement between a successful READ and a REWRITE / DELETE
      * (sequential access) gives 43: IBM's rule is that the LAST input-
      * output statement executed for the file before the REWRITE /
      * DELETE was a successfully executed READ.  Both sides: A3 43, B3
      * 43.  D: READ, failed OPEN (41), REWRITE: model 43 (IBM);
      * GnuCOBOL 00 (G-open41: it keeps the READ across the failed
      * OPEN).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. RM43.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT SF ASSIGN TO 'rm43s.dat'
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS FS1.
           SELECT KF ASSIGN TO 'rm43k.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
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
           MOVE 'AAAAAA' TO S-REC
           WRITE S-REC
           MOVE 'BBBBBB' TO S-REC
           WRITE S-REC
           CLOSE SF
           OPEN I-O SF
           READ SF
           DISPLAY 'A1 READ ' FS1
           WRITE S-REC
           DISPLAY 'A2 WRITE ' FS1
           MOVE 'XXXXXX' TO S-REC
           REWRITE S-REC
           DISPLAY 'A3 REWRITE ' FS1
           READ SF
           DISPLAY 'D1 READ ' FS1
           OPEN I-O SF
           DISPLAY 'D2 OPEN ' FS1
           MOVE 'YYYYYY' TO S-REC
           REWRITE S-REC
           DISPLAY 'D3 REWRITE ' FS1
           CLOSE SF
           OPEN OUTPUT KF
           MOVE 'K01D01' TO K-REC
           WRITE K-REC
           MOVE 'K02D02' TO K-REC
           WRITE K-REC
           CLOSE KF
           OPEN I-O KF
           READ KF
           DISPLAY 'B1 READ ' FS2 ' ' K-REC
           MOVE 'K09D09' TO K-REC
           WRITE K-REC
           DISPLAY 'B2 WRITE ' FS2
           DELETE KF RECORD
           DISPLAY 'B3 DELETE ' FS2
           CLOSE KF
           OPEN INPUT KF
           READ KF
           DISPLAY 'B4 FIRST ' FS2 ' ' K-REC
           CLOSE KF
           STOP RUN.
