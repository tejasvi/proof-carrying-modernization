       IDENTIFICATION DIVISION.
       PROGRAM-ID. P6.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F ASSIGN TO "p6f.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS K
               ALTERNATE RECORD KEY IS A2 WITH DUPLICATES
               FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD F.
       01 R.
          05 K PIC X(3).
          05 A2 PIC X(2).
          05 V PIC X(3).
       WORKING-STORAGE SECTION.
       01 FS PIC XX VALUE "..".
       01 T PIC XX VALUE "..".
       PROCEDURE DIVISION.
       MAIN.
           OPEN OUTPUT F.
           MOVE "K05Bxv1 " TO R. WRITE R.
           MOVE "K02Bxv2 " TO R. WRITE R.
           MOVE "K08Axv3 " TO R. WRITE R.
           MOVE "K01Cxv4 " TO R. WRITE R.
           MOVE "K04Bxv5 " TO R. WRITE R.
           CLOSE F.
           OPEN I-O F.
           MOVE "T1" TO T.
           MOVE "Bx" TO A2.
           START F KEY IS EQUAL TO A2.
           DISPLAY "T1 START " FS.
           PERFORM RN.
           MOVE "K99" TO K.
           READ F KEY IS K INVALID KEY DISPLAY "T1 RK INV " FS.
           PERFORM RN 2 TIMES.
           MOVE "T2" TO T.
           MOVE "zz" TO A2.
           READ F KEY IS A2 INVALID KEY DISPLAY "T2 RK INV " FS.
           PERFORM RN 2 TIMES.
           MOVE "T3" TO T.
           MOVE "K01" TO K.
           START F KEY IS EQUAL TO K.
           DISPLAY "T3 START " FS.
           PERFORM RN.
           MOVE "zz" TO A2.
           READ F KEY IS A2 INVALID KEY DISPLAY "T3 RK INV " FS.
           PERFORM RN 2 TIMES.
           MOVE "T4" TO T.
           MOVE "K98" TO K.
           READ F KEY IS K INVALID KEY DISPLAY "T4 RK INV " FS.
           PERFORM RN 2 TIMES.
           MOVE "T5" TO T.
           MOVE "Ax" TO A2.
           READ F KEY IS A2 INVALID KEY DISPLAY "T5 RK INV " FS.
           DISPLAY "T5 RK " R " " FS.
           MOVE "K97" TO K.
           READ F KEY IS K INVALID KEY DISPLAY "T5 RK INV " FS.
           PERFORM RN 2 TIMES.
           CLOSE F.
           STOP RUN.
       RN.
           READ F NEXT RECORD
             AT END DISPLAY T " RN END " FS
             NOT AT END DISPLAY T " RN " R " " FS
           END-READ.
           DISPLAY T " RN status " FS.
