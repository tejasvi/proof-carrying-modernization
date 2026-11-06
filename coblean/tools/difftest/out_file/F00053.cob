       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00053.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00053_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00053_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
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
           05  TRC PIC X(300) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 340.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           CLOSE XF1
           MOVE XF1-S TO TRC(1:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K02A53B4' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(9:1)
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(10:2)
           MOVE 'K04A2ZG9' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(15:1)
           END-WRITE
           MOVE XF1-S TO TRC(13:2)
           MOVE 'K08A18VJ' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(18:1)
               NOT INVALID KEY MOVE 'N' TO TRC(18:1)
           END-WRITE
           MOVE XF1-S TO TRC(16:2)
           MOVE 'K02A1WBB' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(21:1)
               NOT INVALID KEY MOVE 'N' TO TRC(21:1)
           END-WRITE
           MOVE XF1-S TO TRC(19:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(22:2)
           MOVE 'K05A3U1Y' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(25:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(28:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(31:2)
           MOVE 'K02A12KU' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(36:1)
           END-WRITE
           MOVE XF1-S TO TRC(34:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(37:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(40:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(43:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(46:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(49:2)
           MOVE 'K04LG5' TO XF2-R
           REWRITE XF2-R
               NOT INVALID KEY MOVE 'N' TO TRC(54:1)
           END-REWRITE
           MOVE XF2-S TO TRC(52:2)
           READ XF1
               AT END MOVE 'E' TO TRC(57:1)
           END-READ
           MOVE XF1-S TO TRC(55:2)
           MOVE XF1-R TO TRC(58:8)
           READ XF1
           END-READ
           MOVE XF1-S TO TRC(66:2)
           MOVE XF1-R TO TRC(69:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(77:2)
           READ XF1
           END-READ
           MOVE XF1-S TO TRC(80:2)
           MOVE XF1-R TO TRC(83:8)
           READ XF1 INTO XF1-I
           END-READ
           MOVE XF1-S TO TRC(91:2)
           MOVE XF1-R TO TRC(94:8)
           MOVE XF1-I TO TRC(102:8)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(110:2)
           MOVE 'K05' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(115:1)
           END-READ
           MOVE XF2-S TO TRC(113:2)
           MOVE XF2-R TO TRC(116:6)
           MOVE 'K04' TO XF2-K
           READ XF2 KEY IS XF2-K
           END-READ
           MOVE XF2-S TO TRC(122:2)
           MOVE XF2-R TO TRC(125:6)
           MOVE 'K03' TO XF2-K
           READ XF2
               NOT INVALID KEY MOVE 'N' TO TRC(133:1)
           END-READ
           MOVE XF2-S TO TRC(131:2)
           MOVE XF2-R TO TRC(134:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(140:2)
           MOVE 'K05' TO XF2-K
           READ XF2
           END-READ
           MOVE XF2-S TO TRC(143:2)
           MOVE XF2-R TO TRC(146:6)
           MOVE 'K02OA8' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE XF2-S TO TRC(152:2)
           MOVE 'K03' TO XF2-K
           READ XF2 INTO XF2-I
               INVALID KEY MOVE 'E' TO TRC(157:1)
           END-READ
           MOVE XF2-S TO TRC(155:2)
           MOVE XF2-R TO TRC(158:6)
           MOVE XF2-I TO TRC(164:6)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(170:2)
           READ XF1
               AT END MOVE 'E' TO TRC(175:1)
           END-READ
           MOVE XF1-S TO TRC(173:2)
           MOVE XF1-R TO TRC(176:8)
           READ XF1
               AT END MOVE 'E' TO TRC(186:1)
           END-READ
           MOVE XF1-S TO TRC(184:2)
           MOVE XF1-R TO TRC(187:8)
           READ XF1
               AT END MOVE 'E' TO TRC(197:1)
           END-READ
           MOVE XF1-S TO TRC(195:2)
           MOVE XF1-R TO TRC(198:8)
           READ XF1
               AT END MOVE 'E' TO TRC(208:1)
           END-READ
           MOVE XF1-S TO TRC(206:2)
           MOVE XF1-R TO TRC(209:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(217:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(220:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(223:2)
           MOVE 'K01' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(228:1)
           END-READ
           MOVE XF2-S TO TRC(226:2)
           MOVE XF2-R TO TRC(229:6)
           MOVE 'K02' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(237:1)
           END-READ
           MOVE XF2-S TO TRC(235:2)
           MOVE XF2-R TO TRC(238:6)
           MOVE 'K03' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(246:1)
           END-READ
           MOVE XF2-S TO TRC(244:2)
           MOVE XF2-R TO TRC(247:6)
           MOVE 'K04' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(255:1)
           END-READ
           MOVE XF2-S TO TRC(253:2)
           MOVE XF2-R TO TRC(256:6)
           MOVE 'K05' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(264:1)
           END-READ
           MOVE XF2-S TO TRC(262:2)
           MOVE XF2-R TO TRC(265:6)
           MOVE 'K06' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(273:1)
           END-READ
           MOVE XF2-S TO TRC(271:2)
           MOVE XF2-R TO TRC(274:6)
           MOVE 'K07' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(282:1)
           END-READ
           MOVE XF2-S TO TRC(280:2)
           MOVE XF2-R TO TRC(283:6)
           MOVE 'K08' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(291:1)
           END-READ
           MOVE XF2-S TO TRC(289:2)
           MOVE XF2-R TO TRC(292:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(298:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 340
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
