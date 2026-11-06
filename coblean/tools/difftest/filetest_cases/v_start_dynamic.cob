      * START (record key and a leading part of it) and ACCESS DYNAMIC
      * (random READ, READ NEXT, WRITE before the reading position).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. STK1.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT KF ASSIGN TO 'stk1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS DYNAMIC
               RECORD KEY IS K-KEY
               FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD  KF.
       01  K-REC.
           05  K-KEY.
               10  K-A PIC X(2).
               10  K-B PIC X(1).
           05  K-DATA PIC X(3).
       WORKING-STORAGE SECTION.
       01  FS PIC XX.
       PROCEDURE DIVISION.
           OPEN OUTPUT KF
           MOVE 'AA1D01' TO K-REC
           WRITE K-REC
           MOVE 'AA3D02' TO K-REC
           WRITE K-REC
           MOVE 'AB2D03' TO K-REC
           WRITE K-REC
           MOVE 'AC1D04' TO K-REC
           WRITE K-REC
           MOVE 'BA1D05' TO K-REC
           WRITE K-REC
           CLOSE KF
           OPEN I-O KF
           MOVE 'AB2' TO K-KEY
           START KF KEY IS = K-KEY INVALID KEY DISPLAY 'S1 INV'
           END-START
           DISPLAY 'S1 ' FS
           READ KF NEXT RECORD AT END DISPLAY 'R1 END'
           END-READ
           DISPLAY 'R1 ' FS ' ' K-REC
           MOVE 'AB2' TO K-KEY
           START KF KEY IS > K-KEY
           DISPLAY 'S2 ' FS
           READ KF NEXT
           DISPLAY 'R2 ' FS ' ' K-REC
           MOVE 'AC' TO K-A
           START KF KEY IS NOT < K-A
           DISPLAY 'S3 ' FS
           READ KF NEXT
           DISPLAY 'R3 ' FS ' ' K-REC
           READ KF NEXT
           DISPLAY 'R4 ' FS ' ' K-REC
           READ KF NEXT
           DISPLAY 'R5 ' FS
           MOVE 'ZZ9' TO K-KEY
           START KF KEY IS >= K-KEY INVALID KEY DISPLAY 'S6 INV'
           END-START
           DISPLAY 'S6 ' FS
           READ KF NEXT
           DISPLAY 'R6 ' FS
           MOVE 'AA3' TO K-KEY
           READ KF KEY IS K-KEY
           DISPLAY 'R7 ' FS ' ' K-REC
           READ KF NEXT
           DISPLAY 'R8 ' FS ' ' K-REC
           MOVE 'AA2X02' TO K-REC
           WRITE K-REC
           DISPLAY 'W9 ' FS
           READ KF NEXT
           DISPLAY 'R9 ' FS ' ' K-REC
           MOVE 'AA1' TO K-KEY
           START KF
           DISPLAY 'S10 ' FS
           READ KF NEXT
           DISPLAY 'R10 ' FS ' ' K-REC
           READ KF NEXT
           DISPLAY 'R11 ' FS ' ' K-REC
           CLOSE KF
           STOP RUN.
