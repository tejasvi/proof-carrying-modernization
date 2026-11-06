       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00137.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00137_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00137_2.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00137_3.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF3-K
               ALTERNATE RECORD KEY IS XF3-A
               FILE STATUS IS XF3-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-A PIC X(2).
           05  XF1-D PIC X(3).
       FD  XF2.
       01  XF2-R.
           05  XF2-D PIC X(6).
       FD  XF3.
       01  XF3-R.
           05  XF3-K PIC X(3).
           05  XF3-A PIC X(2).
           05  XF3-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(406) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(8) VALUE SPACES.
           05  XF3-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 464.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           CLOSE XF1
           MOVE XF1-S TO TRC(1:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(4:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(7:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(10:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(13:2)
           MOVE 'K04A6EP8' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(16:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(19:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(22:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(25:2)
           MOVE 'R66IY8' TO XF2-R
           REWRITE XF2-R
           END-REWRITE
           MOVE XF2-S TO TRC(28:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(31:2)
           MOVE 'K04A5YWQ' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(36:1)
               NOT INVALID KEY MOVE 'N' TO TRC(36:1)
           END-WRITE
           MOVE XF1-S TO TRC(34:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(37:2)
           MOVE 'K06A4QFJ' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(42:1)
           END-WRITE
           MOVE XF1-S TO TRC(40:2)
           MOVE '2K0A05' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(43:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(46:2)
           MOVE 'K08' TO XF3-K
           READ XF3 KEY IS XF3-K
               INVALID KEY MOVE 'E' TO TRC(51:1)
           END-READ
           MOVE XF3-S TO TRC(49:2)
           MOVE XF3-R TO TRC(52:8)
           MOVE 'A1' TO XF3-A
           READ XF3 KEY IS XF3-A
           END-READ
           MOVE XF3-S TO TRC(60:2)
           MOVE XF3-R TO TRC(63:8)
           MOVE '10YZTQ' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(71:2)
           MOVE 'K08A2RHR' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(76:1)
               NOT INVALID KEY MOVE 'N' TO TRC(76:1)
           END-WRITE
           MOVE XF1-S TO TRC(74:2)
           MOVE 'KZPG5L' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE XF2-S TO TRC(77:2)
           MOVE 'K06' TO XF3-K
           READ XF3 KEY IS XF3-K
               INVALID KEY MOVE 'E' TO TRC(82:1)
               NOT INVALID KEY MOVE 'N' TO TRC(82:1)
           END-READ
           MOVE XF3-S TO TRC(80:2)
           MOVE XF3-R TO TRC(83:8)
           MOVE 'K02A4URM' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(91:2)
           OPEN EXTEND XF2
           MOVE XF2-S TO TRC(94:2)
           MOVE 'A3' TO XF3-A
           READ XF3 KEY IS XF3-A
           END-READ
           MOVE XF3-S TO TRC(97:2)
           MOVE XF3-R TO TRC(100:8)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(108:2)
           MOVE 'A3' TO XF3-A
           READ XF3 KEY IS XF3-A
               NOT INVALID KEY MOVE 'N' TO TRC(113:1)
           END-READ
           MOVE XF3-S TO TRC(111:2)
           MOVE XF3-R TO TRC(114:8)
           MOVE 'K06A6MI8' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(124:1)
               NOT INVALID KEY MOVE 'N' TO TRC(124:1)
           END-WRITE
           MOVE XF1-S TO TRC(122:2)
           MOVE 'Z7QQN0' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(125:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(128:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(131:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(134:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(137:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(140:2)
           READ XF1
               AT END MOVE 'E' TO TRC(145:1)
           END-READ
           MOVE XF1-S TO TRC(143:2)
           MOVE XF1-R TO TRC(146:8)
           READ XF1
               AT END MOVE 'E' TO TRC(156:1)
           END-READ
           MOVE XF1-S TO TRC(154:2)
           MOVE XF1-R TO TRC(157:8)
           READ XF1
               AT END MOVE 'E' TO TRC(167:1)
           END-READ
           MOVE XF1-S TO TRC(165:2)
           MOVE XF1-R TO TRC(168:8)
           READ XF1
               AT END MOVE 'E' TO TRC(178:1)
           END-READ
           MOVE XF1-S TO TRC(176:2)
           MOVE XF1-R TO TRC(179:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(187:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(190:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(193:2)
           READ XF2
               AT END MOVE 'E' TO TRC(198:1)
           END-READ
           MOVE XF2-S TO TRC(196:2)
           MOVE XF2-R TO TRC(199:6)
           READ XF2
               AT END MOVE 'E' TO TRC(207:1)
           END-READ
           MOVE XF2-S TO TRC(205:2)
           MOVE XF2-R TO TRC(208:6)
           READ XF2
               AT END MOVE 'E' TO TRC(216:1)
           END-READ
           MOVE XF2-S TO TRC(214:2)
           MOVE XF2-R TO TRC(217:6)
           READ XF2
               AT END MOVE 'E' TO TRC(225:1)
           END-READ
           MOVE XF2-S TO TRC(223:2)
           MOVE XF2-R TO TRC(226:6)
           READ XF2
               AT END MOVE 'E' TO TRC(234:1)
           END-READ
           MOVE XF2-S TO TRC(232:2)
           MOVE XF2-R TO TRC(235:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(241:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(244:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(247:2)
           MOVE 'K01' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(252:1)
           END-READ
           MOVE XF3-S TO TRC(250:2)
           MOVE XF3-R TO TRC(253:8)
           MOVE 'K02' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(263:1)
           END-READ
           MOVE XF3-S TO TRC(261:2)
           MOVE XF3-R TO TRC(264:8)
           MOVE 'K03' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(274:1)
           END-READ
           MOVE XF3-S TO TRC(272:2)
           MOVE XF3-R TO TRC(275:8)
           MOVE 'K04' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(285:1)
           END-READ
           MOVE XF3-S TO TRC(283:2)
           MOVE XF3-R TO TRC(286:8)
           MOVE 'K05' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(296:1)
           END-READ
           MOVE XF3-S TO TRC(294:2)
           MOVE XF3-R TO TRC(297:8)
           MOVE 'K06' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(307:1)
           END-READ
           MOVE XF3-S TO TRC(305:2)
           MOVE XF3-R TO TRC(308:8)
           MOVE 'K07' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(318:1)
           END-READ
           MOVE XF3-S TO TRC(316:2)
           MOVE XF3-R TO TRC(319:8)
           MOVE 'K08' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(329:1)
           END-READ
           MOVE XF3-S TO TRC(327:2)
           MOVE XF3-R TO TRC(330:8)
           MOVE 'A1' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(340:1)
           END-READ
           MOVE XF3-S TO TRC(338:2)
           MOVE XF3-R TO TRC(341:8)
           MOVE 'A2' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(351:1)
           END-READ
           MOVE XF3-S TO TRC(349:2)
           MOVE XF3-R TO TRC(352:8)
           MOVE 'A3' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(362:1)
           END-READ
           MOVE XF3-S TO TRC(360:2)
           MOVE XF3-R TO TRC(363:8)
           MOVE 'A4' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(373:1)
           END-READ
           MOVE XF3-S TO TRC(371:2)
           MOVE XF3-R TO TRC(374:8)
           MOVE 'A5' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(384:1)
           END-READ
           MOVE XF3-S TO TRC(382:2)
           MOVE XF3-R TO TRC(385:8)
           MOVE 'A6' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(395:1)
           END-READ
           MOVE XF3-S TO TRC(393:2)
           MOVE XF3-R TO TRC(396:8)
           CLOSE XF3
           MOVE XF3-S TO TRC(404:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 464
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
