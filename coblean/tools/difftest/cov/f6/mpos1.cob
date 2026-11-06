       IDENTIFICATION DIVISION.
       PROGRAM-ID. P6MPOS.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT KF ASSIGN TO "kf.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS K-KEY FILE STATUS IS SK.
       DATA DIVISION.
       FILE SECTION.
       FD  KF.
       01  K-REC.
           05  K-KEY PIC 99.
           05  K-DAT PIC X(3).
       WORKING-STORAGE SECTION.
       01  SK  PIC XX VALUE SPACES.
       PROCEDURE DIVISION.
           OPEN OUTPUT KF
           MOVE 10 TO K-KEY MOVE 'aaa' TO K-DAT WRITE K-REC
           MOVE 20 TO K-KEY MOVE 'bbb' TO K-DAT WRITE K-REC
           MOVE 30 TO K-KEY MOVE 'ccc' TO K-DAT WRITE K-REC
           CLOSE KF
           OPEN I-O KF
           MOVE 15 TO K-KEY START KF KEY IS NOT LESS THAN K-KEY
           DISPLAY 'S1 ' SK '|'
           MOVE 17 TO K-KEY MOVE 'new' TO K-DAT WRITE K-REC
           DISPLAY 'S2 ' SK '|'
           READ KF NEXT RECORD
           DISPLAY 'S3 ' SK ' ' K-REC '|'
           CLOSE KF
           OPEN OUTPUT KF
           MOVE 10 TO K-KEY MOVE 'aaa' TO K-DAT WRITE K-REC
           MOVE 20 TO K-KEY MOVE 'bbb' TO K-DAT WRITE K-REC
           MOVE 30 TO K-KEY MOVE 'ccc' TO K-DAT WRITE K-REC
           CLOSE KF
           OPEN I-O KF
           READ KF NEXT RECORD DISPLAY 'D1 ' SK ' ' K-REC '|'
           DELETE KF RECORD DISPLAY 'D2 ' SK '|'
           MOVE 05 TO K-KEY MOVE 'fiv' TO K-DAT WRITE K-REC
           DISPLAY 'D3 ' SK '|'
           READ KF NEXT RECORD DISPLAY 'D4 ' SK ' ' K-REC '|'
           CLOSE KF
           STOP RUN.
