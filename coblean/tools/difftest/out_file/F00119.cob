       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00119.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00119_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00119_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF2-K.
           SELECT XF3 ASSIGN TO 'F00119_3.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF3-K
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
           05  XF2-K PIC X(3).
           05  XF2-D PIC X(3).
       FD  XF3.
       01  XF3-R.
           05  XF3-K PIC X(3).
           05  XF3-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(313) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(6) VALUE SPACES.
           05  XF3-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 365.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF2
           MOVE '--' TO TRC(1:2)
           MOVE 'K06A69MP' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(6:1)
           END-WRITE
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K07ZZ7' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(9:1)
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE '--' TO TRC(7:2)
           MOVE 'K06EKY' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(10:2)
           MOVE 'K08J9O' TO XF3-R
           REWRITE XF3-R
               INVALID KEY MOVE 'E' TO TRC(15:1)
           END-REWRITE
           MOVE XF3-S TO TRC(13:2)
           DELETE XF3 RECORD
           END-DELETE
           MOVE XF3-S TO TRC(16:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(19:2)
           MOVE 'K08E4R' TO XF3-R
           WRITE XF3-R
               INVALID KEY MOVE 'E' TO TRC(24:1)
           END-WRITE
           MOVE XF3-S TO TRC(22:2)
           MOVE 'K08G2X' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(25:2)
           MOVE 'K06D68' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(30:1)
           END-WRITE
           MOVE '--' TO TRC(28:2)
           MOVE 'K01ON3' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(33:1)
               NOT INVALID KEY MOVE 'N' TO TRC(33:1)
           END-WRITE
           MOVE '--' TO TRC(31:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(34:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(37:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(40:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(43:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(46:2)
           MOVE 'K01' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(51:1)
           END-READ
           MOVE XF1-S TO TRC(49:2)
           MOVE XF1-R TO TRC(52:8)
           MOVE 'K02' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(62:1)
           END-READ
           MOVE XF1-S TO TRC(60:2)
           MOVE XF1-R TO TRC(63:8)
           MOVE 'K03' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(73:1)
           END-READ
           MOVE XF1-S TO TRC(71:2)
           MOVE XF1-R TO TRC(74:8)
           MOVE 'K04' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(84:1)
           END-READ
           MOVE XF1-S TO TRC(82:2)
           MOVE XF1-R TO TRC(85:8)
           MOVE 'K05' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(95:1)
           END-READ
           MOVE XF1-S TO TRC(93:2)
           MOVE XF1-R TO TRC(96:8)
           MOVE 'K06' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(106:1)
           END-READ
           MOVE XF1-S TO TRC(104:2)
           MOVE XF1-R TO TRC(107:8)
           MOVE 'K07' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(117:1)
           END-READ
           MOVE XF1-S TO TRC(115:2)
           MOVE XF1-R TO TRC(118:8)
           MOVE 'K08' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(128:1)
           END-READ
           MOVE XF1-S TO TRC(126:2)
           MOVE XF1-R TO TRC(129:8)
           MOVE 'A1' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(139:1)
           END-READ
           MOVE XF1-S TO TRC(137:2)
           MOVE XF1-R TO TRC(140:8)
           MOVE 'A2' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(150:1)
           END-READ
           MOVE XF1-S TO TRC(148:2)
           MOVE XF1-R TO TRC(151:8)
           MOVE 'A3' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(161:1)
           END-READ
           MOVE XF1-S TO TRC(159:2)
           MOVE XF1-R TO TRC(162:8)
           MOVE 'A4' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(172:1)
           END-READ
           MOVE XF1-S TO TRC(170:2)
           MOVE XF1-R TO TRC(173:8)
           MOVE 'A5' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(183:1)
           END-READ
           MOVE XF1-S TO TRC(181:2)
           MOVE XF1-R TO TRC(184:8)
           MOVE 'A6' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(194:1)
           END-READ
           MOVE XF1-S TO TRC(192:2)
           MOVE XF1-R TO TRC(195:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(203:2)
           CLOSE XF2
           MOVE '--' TO TRC(206:2)
           OPEN INPUT XF2
           MOVE '--' TO TRC(209:2)
           MOVE 'K01' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(214:1)
           END-READ
           MOVE '--' TO TRC(212:2)
           MOVE XF2-R TO TRC(215:6)
           MOVE 'K02' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(223:1)
           END-READ
           MOVE '--' TO TRC(221:2)
           MOVE XF2-R TO TRC(224:6)
           MOVE 'K03' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(232:1)
           END-READ
           MOVE '--' TO TRC(230:2)
           MOVE XF2-R TO TRC(233:6)
           MOVE 'K04' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(241:1)
           END-READ
           MOVE '--' TO TRC(239:2)
           MOVE XF2-R TO TRC(242:6)
           MOVE 'K05' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(250:1)
           END-READ
           MOVE '--' TO TRC(248:2)
           MOVE XF2-R TO TRC(251:6)
           MOVE 'K06' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(259:1)
           END-READ
           MOVE '--' TO TRC(257:2)
           MOVE XF2-R TO TRC(260:6)
           MOVE 'K07' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(268:1)
           END-READ
           MOVE '--' TO TRC(266:2)
           MOVE XF2-R TO TRC(269:6)
           MOVE 'K08' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(277:1)
           END-READ
           MOVE '--' TO TRC(275:2)
           MOVE XF2-R TO TRC(278:6)
           CLOSE XF2
           MOVE '--' TO TRC(284:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(287:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(290:2)
           READ XF3
               AT END MOVE 'E' TO TRC(295:1)
           END-READ
           MOVE XF3-S TO TRC(293:2)
           MOVE XF3-R TO TRC(296:6)
           READ XF3
               AT END MOVE 'E' TO TRC(304:1)
           END-READ
           MOVE XF3-S TO TRC(302:2)
           MOVE XF3-R TO TRC(305:6)
           CLOSE XF3
           MOVE XF3-S TO TRC(311:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 365
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
