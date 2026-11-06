       IDENTIFICATION DIVISION.
       PROGRAM-ID. P2.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F ASSIGN TO "p2f.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS K
               ALTERNATE RECORD KEY IS A1
               ALTERNATE RECORD KEY IS A2 WITH DUPLICATES
               FILE STATUS IS FS.
           SELECT G ASSIGN TO "p2g.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS GK
               ALTERNATE RECORD KEY IS GA WITH DUPLICATES
               FILE STATUS IS GS.
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
       FD G.
       01 GR.
          05 GK PIC X(3).
          05 GA PIC X(3).
          05 GV PIC X(3).
       WORKING-STORAGE SECTION.
       01 FS PIC XX VALUE "..".
       01 GS PIC XX VALUE "..".
       01 T PIC XX VALUE "..".
       PROCEDURE DIVISION.
       MAIN.
           OPEN OUTPUT F.
           MOVE "W1" TO T.
           MOVE "K05a05BX v1 " TO R. PERFORM WR.
           MOVE "K02a02BA v2 " TO R. PERFORM WR.
           MOVE "K08a08A  v3 " TO R. PERFORM WR.
           MOVE "K01a01C  v4 " TO R. PERFORM WR.
           MOVE "K04a04BA v5 " TO R. PERFORM WR.
           MOVE "K07a07A  v6 " TO R. PERFORM WR.
           MOVE "K06a06A  v7 " TO R. PERFORM WR.
           CLOSE F.
           OPEN I-O F.
           MOVE "T1" TO T.
           MOVE "a99" TO A1.
           START F KEY IS NOT LESS THAN A1
             INVALID KEY DISPLAY "T1 START INV " FS
           END-START.
           PERFORM RN 2 TIMES.
           MOVE "K99" TO K.
           START F KEY IS EQUAL TO K
             INVALID KEY DISPLAY "T1 START K INV " FS
           END-START.
           PERFORM RN 2 TIMES.
           MOVE "T2" TO T.
           MOVE "x  " TO A2.
           READ F KEY IS A2 INVALID KEY DISPLAY "T2 READ INV " FS
           END-READ.
           PERFORM RN 2 TIMES.
           MOVE "K99" TO K.
           READ F INVALID KEY DISPLAY "T2 READ K INV " FS
           END-READ.
           PERFORM RN 2 TIMES.
           MOVE "T3" TO T.
           MOVE "A  " TO A2.
           START F KEY IS GREATER THAN A2
             INVALID KEY DISPLAY "T3 START INV " FS
           END-START.
           PERFORM RN 2 TIMES.
           MOVE "T4" TO T.
           MOVE "B" TO A2P.
           START F KEY IS EQUAL TO A2P
             INVALID KEY DISPLAY "T4 START INV " FS
           END-START.
           PERFORM RN 3 TIMES.
           MOVE "T5" TO T.
           MOVE "K08" TO K.
           READ F INVALID KEY DISPLAY "T5 READ INV " FS END-READ.
           MOVE "v8 " TO V.
           REWRITE R INVALID KEY DISPLAY "T5 RW INV " FS END-REWRITE.
           DISPLAY "T5 RW " FS.
           MOVE "K01" TO K.
           READ F INVALID KEY DISPLAY "T5 READ INV " FS END-READ.
           MOVE "A  " TO A2.
           REWRITE R INVALID KEY DISPLAY "T5 RW INV " FS END-REWRITE.
           DISPLAY "T5 RW " FS.
           MOVE "K07" TO K.
           DELETE F INVALID KEY DISPLAY "T5 DEL INV " FS END-DELETE.
           MOVE "K07a07A  v9 " TO R. PERFORM WR.
           MOVE "A  " TO A2.
           START F KEY IS EQUAL TO A2
             INVALID KEY DISPLAY "T5 START INV " FS
           END-START.
           PERFORM RN 6 TIMES.
           PERFORM RN 2 TIMES.
           MOVE "T6" TO T.
           MOVE "B  " TO A2.
           START F KEY IS NOT LESS THAN A2
             INVALID KEY DISPLAY "T6 START INV " FS
           END-START.
           CLOSE F.
           OPEN INPUT F.
           PERFORM RN 2 TIMES.
           CLOSE F.
           OPEN OUTPUT G.
           MOVE "T7" TO T.
           MOVE "G01B  g1 " TO GR. PERFORM GW.
           MOVE "G02A  g2 " TO GR. PERFORM GW.
           MOVE "G03B  g3 " TO GR. PERFORM GW.
           MOVE "G04A  g4 " TO GR. PERFORM GW.
           MOVE "G05C  g5 " TO GR. PERFORM GW.
           CLOSE G.
           OPEN I-O G.
           MOVE "B  " TO GA.
           START G KEY IS EQUAL TO GA
             INVALID KEY DISPLAY "T7 START INV " GS
           END-START.
           DISPLAY "T7 START " GS.
           PERFORM GN 1 TIMES.
           MOVE "g6 " TO GV.
           REWRITE GR INVALID KEY DISPLAY "T7 RW INV " GS END-REWRITE.
           DISPLAY "T7 RW " GS.
           PERFORM GN 1 TIMES.
           DELETE G RECORD INVALID KEY DISPLAY "T7 DEL INV " GS
           END-DELETE.
           DISPLAY "T7 DEL " GS.
           PERFORM GN 3 TIMES.
           CLOSE G.
           OPEN INPUT G.
           MOVE "T8" TO T.
           PERFORM GN 6 TIMES.
           CLOSE G.
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
           DISPLAY T " RN status " FS.
       GW.
           WRITE GR INVALID KEY DISPLAY T " GWRITE INV " GR " " GS
             NOT INVALID KEY DISPLAY T " GWRITE OK " GR " " GS
           END-WRITE.
       GN.
           READ G NEXT RECORD
             AT END DISPLAY T " GN END " GS
             NOT AT END DISPLAY T " GN " GR " " GS
           END-READ.
           DISPLAY T " GN status " GS.
