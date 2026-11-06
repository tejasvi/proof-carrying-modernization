      * Front end (fixed 10-23): NOT INVALID KEY used to be extracted as
      * INVALID KEY (parser.phrase with prefixes=() took NOT for a
      * prefix).  Expected on both sides: W1 NOT-INVALID / W2 INVALID.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. RFE1.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT KF ASSIGN TO 'rfe1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS K-KEY
               FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD  KF.
       01  K-REC.
           05  K-KEY   PIC X(3).
           05  K-DATA  PIC X(3).
       WORKING-STORAGE SECTION.
       01  FS PIC XX.
       PROCEDURE DIVISION.
           OPEN OUTPUT KF
           MOVE 'K01D01' TO K-REC
           WRITE K-REC
               INVALID KEY DISPLAY 'W1 INVALID'
               NOT INVALID KEY DISPLAY 'W1 NOT-INVALID'
           END-WRITE
           WRITE K-REC
               INVALID KEY DISPLAY 'W2 INVALID'
               NOT INVALID KEY DISPLAY 'W2 NOT-INVALID'
           END-WRITE
           CLOSE KF
           STOP RUN.
