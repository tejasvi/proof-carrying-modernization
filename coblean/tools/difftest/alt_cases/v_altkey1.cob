       IDENTIFICATION DIVISION.
       PROGRAM-ID. P1.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F ASSIGN TO "p1f.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS K
               ALTERNATE RECORD KEY IS A1
               ALTERNATE RECORD KEY IS A2 WITH DUPLICATES
               FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD F.
       01 R.
          05 K PIC X(3).
          05 A1 PIC X(3).
          05 A2.
             10 A2P PIC X(1).
             10 A2R PIC X(2).
          05 V PIC X(3).
       WORKING-STORAGE SECTION.
       01 FS PIC XX VALUE "..".
       01 T PIC XX VALUE "..".
       01 N PIC 9 VALUE 0.
       PROCEDURE DIVISION.
       MAIN.
           OPEN OUTPUT F.
           MOVE "W1" TO T.
           MOVE "K05a05B  v1 " TO R. PERFORM WR.
           MOVE "K02a02B  v2 " TO R. PERFORM WR.
           MOVE "K08a08A  v3 " TO R. PERFORM WR.
           MOVE "K01a01C  v4 " TO R. PERFORM WR.
           MOVE "K04a04B  v5 " TO R. PERFORM WR.
           MOVE "K07a07A  v6 " TO R. PERFORM WR.
           CLOSE F.
           OPEN I-O F.
           MOVE "T1" TO T.
           MOVE "B  " TO A2.
           START F KEY IS EQUAL TO A2
             INVALID KEY DISPLAY "T1 START INV " FS
             NOT INVALID KEY DISPLAY "T1 START OK " FS
           END-START.
           PERFORM RN 4 TIMES.
           MOVE "T2" TO T.
           MOVE "a03" TO A1.
           START F KEY IS GREATER THAN A1
             INVALID KEY DISPLAY "T2 START INV " FS
           END-START.
           DISPLAY "T2 START " FS.
           PERFORM RN 2 TIMES.
           MOVE "T3" TO T.
           MOVE "A  " TO A2.
           READ F KEY IS A2
             INVALID KEY DISPLAY "T3 READ INV " FS
           END-READ.
           DISPLAY "T3 READKEY " R " " FS.
           PERFORM RN 2 TIMES.
           MOVE "T4" TO T.
           MOVE "B" TO A2P.
           START F KEY IS EQUAL TO A2P
             INVALID KEY DISPLAY "T4 START INV " FS
           END-START.
           DISPLAY "T4 START " FS.
           PERFORM RN 1 TIMES.
           MOVE "T5" TO T.
           MOVE "B  " TO A2.
           START F KEY IS EQUAL TO A2
             INVALID KEY DISPLAY "T5 START INV " FS
           END-START.
           DISPLAY "T5 START " FS.
           PERFORM RN 1 TIMES.
           MOVE "K03a03B  v7 " TO R. PERFORM WR.
           MOVE "K02" TO K.
           DELETE F INVALID KEY DISPLAY "T5 DEL INV " FS END-DELETE.
           DISPLAY "T5 DEL " FS.
           PERFORM RN 3 TIMES.
           MOVE "T6" TO T.
           MOVE "A  " TO A2.
           START F KEY IS EQUAL TO A2
             INVALID KEY DISPLAY "T6 START INV " FS
           END-START.
           DISPLAY "T6 START " FS.
           PERFORM RN 1 TIMES.
           MOVE "C  " TO A2.
           REWRITE R INVALID KEY DISPLAY "T6 RW INV " FS END-REWRITE.
           DISPLAY "T6 RW " FS.
           PERFORM RN 7 TIMES.
           MOVE "T7" TO T.
           MOVE "a99" TO A1.
           START F KEY IS NOT LESS THAN A1
             INVALID KEY DISPLAY "T7 START INV " FS
           END-START.
           DISPLAY "T7 START " FS.
           PERFORM RN 1 TIMES.
           MOVE "T8" TO T.
           MOVE "B  " TO A2.
           START F KEY IS EQUAL TO A2
             INVALID KEY DISPLAY "T8 START INV " FS
           END-START.
           MOVE "K04" TO K.
           READ F INVALID KEY DISPLAY "T8 READ INV " FS END-READ.
           DISPLAY "T8 READKEY " R " " FS.
           PERFORM RN 2 TIMES.
           MOVE "T9" TO T.
           MOVE "K05" TO K.
           READ F INVALID KEY DISPLAY "T9 READ INV " FS END-READ.
           DISPLAY "T9 READKEY " R " " FS.
           REWRITE R INVALID KEY DISPLAY "T9 RW INV " FS END-REWRITE.
           DISPLAY "T9 RW same B " FS.
           MOVE "K07" TO K.
           READ F INVALID KEY DISPLAY "T9 READ INV " FS END-READ.
           MOVE "B  " TO A2.
           REWRITE R INVALID KEY DISPLAY "T9 RW INV " FS END-REWRITE.
           DISPLAY "T9 RW to B " FS.
           MOVE "K09a09Z  v8 " TO R. PERFORM WR.
           MOVE "K10a10Z  v9 " TO R. PERFORM WR.
           MOVE "K11a05Y  v9 " TO R. PERFORM WR.
           CLOSE F.
           STOP RUN.
       WR.
           WRITE R INVALID KEY DISPLAY T " WRITE INV " R " " FS
             NOT INVALID KEY DISPLAY T " WRITE OK " R " " FS
           END-WRITE.
       RN.
           READ F NEXT RECORD
             AT END DISPLAY T " RN END " FS
             NOT AT END DISPLAY T " RN " R " " FS
           END-READ.
