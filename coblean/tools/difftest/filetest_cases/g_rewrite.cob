      * GnuCOBOL REWRITE deviations (BDB):
      * G-rwkey, ACCESS SEQUENTIAL, no alternate key: READ K10, REWRITE with
      *     record key K20.  IBM 21 (key changed since the READ), file
      *     unchanged; model 21.  GnuCOBOL 22 and K10 is deleted (F-reads show
      *     K20 only).
      * G-rwalt, ACCESS SEQUENTIAL with an alternate key: READ, REWRITE with
      *     the same keys.  IBM 00; model 00.  GnuCOBOL prints 'BDB0631 Cursor
      *     position must be set before performing this operation' on stderr,
      *     status 22, record unchanged.
      * G-rw21, ACCESS RANDOM: REWRITE of a missing record key.  IBM 23
      *     (record not found); model 23.  GnuCOBOL 21 (22 if the alternate
      *     key of the new record is in use).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. RREWRITE.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT KF ASSIGN TO 'rrw1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS K-KEY
               FILE STATUS IS FS1.
           SELECT AF ASSIGN TO 'rrw2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS A-KEY
               ALTERNATE RECORD KEY IS A-ALT
               FILE STATUS IS FS2.
           SELECT QF ASSIGN TO 'rrw3.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS Q-KEY
               FILE STATUS IS FS3.
       DATA DIVISION.
       FILE SECTION.
       FD  KF.
       01  K-REC.
           05  K-KEY   PIC X(3).
           05  K-DATA  PIC X(3).
       FD  AF.
       01  A-REC.
           05  A-KEY   PIC X(3).
           05  A-ALT   PIC X(2).
           05  A-DATA  PIC X(3).
       FD  QF.
       01  Q-REC.
           05  Q-KEY   PIC X(3).
           05  Q-DATA  PIC X(3).
       WORKING-STORAGE SECTION.
       01  FS1 PIC XX.
       01  FS2 PIC XX.
       01  FS3 PIC XX.
       PROCEDURE DIVISION.
           OPEN OUTPUT KF
           MOVE 'K10D01' TO K-REC
           WRITE K-REC
           MOVE 'K20D02' TO K-REC
           WRITE K-REC
           CLOSE KF
           OPEN I-O KF
           READ KF
           DISPLAY 'K1 READ ' FS1 ' ' K-REC
           MOVE 'K20D99' TO K-REC
           REWRITE K-REC
           DISPLAY 'K2 REWRITE-KEY-CHANGED ' FS1
           CLOSE KF
           OPEN INPUT KF
           READ KF
           DISPLAY 'F1 ' FS1 ' ' K-REC
           READ KF
           DISPLAY 'F2 ' FS1 ' ' K-REC
           CLOSE KF
           OPEN OUTPUT AF
           MOVE 'K01A1D01' TO A-REC
           WRITE A-REC
           CLOSE AF
           OPEN I-O AF
           READ AF
           DISPLAY 'A1 READ ' FS2 ' ' A-REC
           MOVE 'K01A1NEW' TO A-REC
           REWRITE A-REC
           DISPLAY 'A2 REWRITE-SAME-KEYS ' FS2
           CLOSE AF
           OPEN INPUT AF
           READ AF
           DISPLAY 'A3 ' FS2 ' ' A-REC
           CLOSE AF
           OPEN OUTPUT QF
           MOVE 'K01D01' TO Q-REC
           WRITE Q-REC
           CLOSE QF
           OPEN I-O QF
           MOVE 'K06D06' TO Q-REC
           REWRITE Q-REC
           DISPLAY 'Q1 REWRITE-MISSING ' FS3
           CLOSE QF
           STOP RUN.
