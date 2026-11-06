       IDENTIFICATION DIVISION.
       PROGRAM-ID. P5.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT G ASSIGN TO "p5g.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS GK
               ALTERNATE RECORD KEY IS GB WITH DUPLICATES
               FILE STATUS IS GS.
       DATA DIVISION.
       FILE SECTION.
       FD G.
       01 GR.
          05 GK PIC X(3).
          05 GB PIC X(2).
          05 GV PIC X(3).
       WORKING-STORAGE SECTION.
       01 GS PIC XX VALUE "..".
       01 T PIC XX VALUE "..".
       PROCEDURE DIVISION.
       MAIN.
           OPEN OUTPUT G.
           MOVE "G01Bxg1 " TO GR. WRITE GR. DISPLAY "W " GS.
           MOVE "G02Axg2 " TO GR. WRITE GR. DISPLAY "W " GS.
           MOVE "G03Bxg3 " TO GR. WRITE GR. DISPLAY "W " GS.
           MOVE "G04Axg4 " TO GR. WRITE GR. DISPLAY "W " GS.
           MOVE "G05Bxg5 " TO GR. WRITE GR. DISPLAY "W " GS.
           CLOSE G.
           OPEN I-O G.
           MOVE "T1" TO T.
           MOVE "Bx" TO GB.
           START G KEY IS EQUAL TO GB.
           DISPLAY "T1 START " GS.
           PERFORM GN.
           MOVE "Ax" TO GB.
           REWRITE GR. DISPLAY "T1 RW toA " GS.
           PERFORM GN.
           MOVE "Cx" TO GB.
           REWRITE GR. DISPLAY "T1 RW toC " GS.
           PERFORM GN 3 TIMES.
           MOVE "T2" TO T.
           MOVE "Ax" TO GB.
           START G KEY IS EQUAL TO GB.
           DISPLAY "T2 START " GS.
           PERFORM GN 6 TIMES.
           MOVE "T3" TO T.
           MOVE "G02" TO GK.
           START G KEY IS GREATER THAN GK.
           DISPLAY "T3 START " GS.
           PERFORM GN 2 TIMES.
           DELETE G RECORD. DISPLAY "T3 DEL " GS.
           PERFORM GN 1 TIMES.
           MOVE "T4" TO T.
           MOVE "Cx" TO GB.
           START G KEY IS NOT LESS THAN GB.
           DISPLAY "T4 START " GS.
           PERFORM GN 3 TIMES.
           CLOSE G.
           STOP RUN.
       GN.
           READ G NEXT RECORD
             AT END DISPLAY T " GN END " GS
             NOT AT END DISPLAY T " GN " GR " " GS
           END-READ.
