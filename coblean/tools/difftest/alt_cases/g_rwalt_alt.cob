       IDENTIFICATION DIVISION.
       PROGRAM-ID. P4.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT G ASSIGN TO "p4g.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS GK
               ALTERNATE RECORD KEY IS GA
               FILE STATUS IS GS.
           SELECT H ASSIGN TO "p4h.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS HK
               ALTERNATE RECORD KEY IS HA
               ALTERNATE RECORD KEY IS HB WITH DUPLICATES
               FILE STATUS IS HS.
       DATA DIVISION.
       FILE SECTION.
       FD G.
       01 GR.
          05 GK PIC X(3).
          05 GA PIC X(3).
          05 GV PIC X(3).
       FD H.
       01 HR.
          05 HK PIC X(3).
          05 HA PIC X(3).
          05 HB PIC X(3).
          05 HV PIC X(3).
       WORKING-STORAGE SECTION.
       01 GS PIC XX VALUE "..".
       01 HS PIC XX VALUE "..".
       01 T PIC XX VALUE "..".
       PROCEDURE DIVISION.
       MAIN.
           OPEN OUTPUT G.
           MOVE "G01b01g1 " TO GR. WRITE GR. DISPLAY "W " GS.
           MOVE "G02a02g2 " TO GR. WRITE GR. DISPLAY "W " GS.
           MOVE "G03c03g3 " TO GR. WRITE GR. DISPLAY "W " GS.
           MOVE "G04a01g4 " TO GR. WRITE GR. DISPLAY "W " GS.
           CLOSE G.
           OPEN I-O G.
           MOVE "T1" TO T.
           PERFORM GN.
           MOVE "x1 " TO GV.
           REWRITE GR. DISPLAY "T1 RW " GS.
           PERFORM GN.
           MOVE "a09" TO GA.
           REWRITE GR. DISPLAY "T1 RW newalt " GS.
           PERFORM GN.
           MOVE "a01" TO GA.
           REWRITE GR. DISPLAY "T1 RW usedalt " GS.
           MOVE "T2" TO T.
           MOVE "a02" TO GA.
           START G KEY IS NOT LESS THAN GA.
           DISPLAY "T2 START " GS.
           PERFORM GN.
           MOVE "x2 " TO GV.
           REWRITE GR. DISPLAY "T2 RW " GS.
           PERFORM GN.
           DELETE G RECORD. DISPLAY "T2 DEL " GS.
           PERFORM GN 2 TIMES.
           CLOSE G.
           OPEN INPUT G.
           MOVE "T3" TO T.
           PERFORM GN 5 TIMES.
           CLOSE G.
           OPEN OUTPUT H.
           MOVE "H01a01B  h1 " TO HR. WRITE HR. DISPLAY "HW " HS.
           MOVE "H02a02A  h2 " TO HR. WRITE HR. DISPLAY "HW " HS.
           MOVE "H03a03B  h3 " TO HR. WRITE HR. DISPLAY "HW " HS.
           CLOSE H.
           OPEN I-O H.
           MOVE "T4" TO T.
           PERFORM HN.
           MOVE "y1 " TO HV.
           REWRITE HR. DISPLAY "T4 RW " HS.
           MOVE "B  " TO HB.
           START H KEY IS EQUAL TO HB.
           DISPLAY "T4 START " HS.
           PERFORM HN.
           MOVE "y2 " TO HV.
           REWRITE HR. DISPLAY "T4 RW " HS.
           PERFORM HN.
           MOVE "A  " TO HB.
           REWRITE HR. DISPLAY "T4 RW toA " HS.
           PERFORM HN 2 TIMES.
           CLOSE H.
           OPEN INPUT H.
           MOVE "T5" TO T.
           PERFORM HN 4 TIMES.
           CLOSE H.
           STOP RUN.
       GN.
           READ G NEXT RECORD
             AT END DISPLAY T " GN END " GS
             NOT AT END DISPLAY T " GN " GR " " GS
           END-READ.
       HN.
           READ H NEXT RECORD
             AT END DISPLAY T " HN END " HS
             NOT AT END DISPLAY T " HN " HR " " HS
           END-READ.
