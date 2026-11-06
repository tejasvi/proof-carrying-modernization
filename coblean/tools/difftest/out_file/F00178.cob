       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00178.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00178_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00178_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF2-K
               FILE STATUS IS XF2-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-A PIC X(2).
           05  XF1-D PIC X(3).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(176) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 216.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           MOVE 'K05X7Y' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(6:1)
           END-WRITE
           MOVE XF2-S TO TRC(4:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(7:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(10:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(13:2)
           READ XF2 NEXT RECORD INTO XF2-I
           END-READ
           MOVE XF2-S TO TRC(16:2)
           MOVE XF2-R TO TRC(19:6)
           MOVE XF2-I TO TRC(25:6)
           MOVE 'K04A1PCA' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(33:1)
           END-WRITE
           MOVE XF1-S TO TRC(31:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(34:2)
           MOVE 'K05A25E1' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(39:1)
           END-WRITE
           MOVE XF1-S TO TRC(37:2)
           MOVE 'K06A2PND' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(40:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(43:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(46:2)
           DELETE XF2 RECORD
           END-DELETE
           MOVE XF2-S TO TRC(49:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(52:2)
           MOVE 'K08A1ROY' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(55:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(58:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(61:2)
           MOVE 'K08A2GHJ' TO XF1-R
           REWRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(66:1)
               NOT INVALID KEY MOVE 'N' TO TRC(66:1)
           END-REWRITE
           MOVE XF1-S TO TRC(64:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(67:2)
           READ XF2 NEXT RECORD
               AT END MOVE 'E' TO TRC(72:1)
               NOT AT END MOVE 'N' TO TRC(72:1)
           END-READ
           MOVE XF2-S TO TRC(70:2)
           MOVE XF2-R TO TRC(73:6)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(79:2)
           READ XF2 INTO XF2-I
           END-READ
           MOVE XF2-S TO TRC(82:2)
           MOVE XF2-R TO TRC(85:6)
           MOVE XF2-I TO TRC(91:6)
           READ XF1 NEXT RECORD
           END-READ
           MOVE XF1-S TO TRC(97:2)
           MOVE XF1-R TO TRC(100:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(108:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(111:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(114:2)
           READ XF1
               AT END MOVE 'E' TO TRC(119:1)
           END-READ
           MOVE XF1-S TO TRC(117:2)
           MOVE XF1-R TO TRC(120:8)
           READ XF1
               AT END MOVE 'E' TO TRC(130:1)
           END-READ
           MOVE XF1-S TO TRC(128:2)
           MOVE XF1-R TO TRC(131:8)
           READ XF1
               AT END MOVE 'E' TO TRC(141:1)
           END-READ
           MOVE XF1-S TO TRC(139:2)
           MOVE XF1-R TO TRC(142:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(150:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(153:2)
           READ XF2
               AT END MOVE 'E' TO TRC(158:1)
           END-READ
           MOVE XF2-S TO TRC(156:2)
           MOVE XF2-R TO TRC(159:6)
           READ XF2
               AT END MOVE 'E' TO TRC(167:1)
           END-READ
           MOVE XF2-S TO TRC(165:2)
           MOVE XF2-R TO TRC(168:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(174:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 216
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
