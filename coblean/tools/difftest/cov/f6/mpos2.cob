       IDENTIFICATION DIVISION.
       PROGRAM-ID. MPOS2.
      * M-pos variants: START KEY > (strict) then a WRITE landing at the
      * position; START KEY = then a WRITE before it; READ, WRITE of a key
      * before the last record read (no defect expected: positioned after
      * the record read).
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT KF ASSIGN TO "kf2.dat"
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
           PERFORM LOAD
           OPEN I-O KF
           MOVE 10 TO K-KEY START KF KEY IS GREATER THAN K-KEY
           DISPLAY 'A1 ' SK '|'
           MOVE 15 TO K-KEY MOVE 'new' TO K-DAT WRITE K-REC
           DISPLAY 'A2 ' SK '|'
           READ KF NEXT RECORD DISPLAY 'A3 ' SK ' ' K-REC '|'
           READ KF NEXT RECORD DISPLAY 'A4 ' SK ' ' K-REC '|'
           CLOSE KF
           PERFORM LOAD
           OPEN I-O KF
           MOVE 30 TO K-KEY START KF KEY IS EQUAL TO K-KEY
           DISPLAY 'B1 ' SK '|'
           MOVE 25 TO K-KEY MOVE 'new' TO K-DAT WRITE K-REC
           DISPLAY 'B2 ' SK '|'
           READ KF NEXT RECORD DISPLAY 'B3 ' SK ' ' K-REC '|'
           CLOSE KF
           PERFORM LOAD
           OPEN I-O KF
           READ KF NEXT RECORD DISPLAY 'C1 ' SK ' ' K-REC '|'
           READ KF NEXT RECORD DISPLAY 'C2 ' SK ' ' K-REC '|'
           MOVE 15 TO K-KEY MOVE 'new' TO K-DAT WRITE K-REC
           DISPLAY 'C3 ' SK '|'
           MOVE 25 TO K-KEY MOVE 'nxt' TO K-DAT WRITE K-REC
           DISPLAY 'C4 ' SK '|'
           READ KF NEXT RECORD DISPLAY 'C5 ' SK ' ' K-REC '|'
           CLOSE KF
           STOP RUN.
       LOAD.
           OPEN OUTPUT KF
           MOVE 10 TO K-KEY MOVE 'aaa' TO K-DAT WRITE K-REC
           MOVE 20 TO K-KEY MOVE 'bbb' TO K-DAT WRITE K-REC
           MOVE 30 TO K-KEY MOVE 'ccc' TO K-DAT WRITE K-REC
           CLOSE KF.
