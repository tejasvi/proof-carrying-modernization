       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00078.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00078_1.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00078_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF2-K
               ALTERNATE RECORD KEY IS XF2-A
               FILE STATUS IS XF2-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-D PIC X(6).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-A PIC X(2).
           05  XF2-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(345) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 385.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           CLOSE XF2
           MOVE XF2-S TO TRC(1:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(4:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(7:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(10:2)
           MOVE 'K02' TO XF2-K
           READ XF2 KEY IS XF2-K
               INVALID KEY MOVE 'E' TO TRC(15:1)
               NOT INVALID KEY MOVE 'N' TO TRC(15:1)
           END-READ
           MOVE XF2-S TO TRC(13:2)
           MOVE XF2-R TO TRC(16:8)
           MOVE 'K03A3XRC' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(24:2)
           MOVE 'K02A48CU' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(29:1)
               NOT INVALID KEY MOVE 'N' TO TRC(29:1)
           END-WRITE
           MOVE XF2-S TO TRC(27:2)
           MOVE 'K03' TO XF2-K
           READ XF2 KEY IS XF2-K
               INVALID KEY MOVE 'E' TO TRC(32:1)
               NOT INVALID KEY MOVE 'N' TO TRC(32:1)
           END-READ
           MOVE XF2-S TO TRC(30:2)
           MOVE XF2-R TO TRC(33:8)
           MOVE 'K07A5PTL' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(43:1)
               NOT INVALID KEY MOVE 'N' TO TRC(43:1)
           END-WRITE
           MOVE XF2-S TO TRC(41:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(44:2)
           MOVE 'K02A57TR' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(49:1)
           END-WRITE
           MOVE XF2-S TO TRC(47:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(50:2)
           READ XF1
               AT END MOVE 'E' TO TRC(55:1)
           END-READ
           MOVE XF1-S TO TRC(53:2)
           MOVE XF1-R TO TRC(56:6)
           READ XF1
               AT END MOVE 'E' TO TRC(64:1)
           END-READ
           MOVE XF1-S TO TRC(62:2)
           MOVE XF1-R TO TRC(65:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(71:2)
           MOVE 'YKK496' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(74:2)
           MOVE 'K03A6OKF' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(79:1)
           END-WRITE
           MOVE XF2-S TO TRC(77:2)
           MOVE 'KHQXT6' TO XF1-R
           REWRITE XF1-R
           END-REWRITE
           MOVE XF1-S TO TRC(80:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(83:2)
           READ XF1
               AT END MOVE 'E' TO TRC(88:1)
           END-READ
           MOVE XF1-S TO TRC(86:2)
           MOVE XF1-R TO TRC(89:6)
           MOVE 'K03' TO XF2-K
           READ XF2
           END-READ
           MOVE XF2-S TO TRC(95:2)
           MOVE XF2-R TO TRC(98:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(106:2)
           MOVE 'K05A2YGD' TO XF2-W
           REWRITE XF2-R FROM XF2-W
               NOT INVALID KEY MOVE 'N' TO TRC(111:1)
           END-REWRITE
           MOVE XF2-S TO TRC(109:2)
           MOVE 'K05' TO XF2-K
           DELETE XF2 RECORD
               INVALID KEY MOVE 'E' TO TRC(114:1)
           END-DELETE
           MOVE XF2-S TO TRC(112:2)
           MOVE 'HX3IMS' TO XF1-W
           REWRITE XF1-R FROM XF1-W
           END-REWRITE
           MOVE XF1-S TO TRC(115:2)
           MOVE 'MMGW0K' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(118:2)
           MOVE 'K02A6Y6T' TO XF2-W
           REWRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(123:1)
               NOT INVALID KEY MOVE 'N' TO TRC(123:1)
           END-REWRITE
           MOVE XF2-S TO TRC(121:2)
           MOVE 'K07' TO XF2-K
           DELETE XF2 RECORD
           END-DELETE
           MOVE XF2-S TO TRC(124:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(127:2)
           MOVE 'K01' TO XF2-K
           READ XF2 KEY IS XF2-K
               INVALID KEY MOVE 'E' TO TRC(132:1)
           END-READ
           MOVE XF2-S TO TRC(130:2)
           MOVE XF2-R TO TRC(133:8)
           MOVE '8PGCBK' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(141:2)
           MOVE 'KX9GSI' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(144:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(147:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(150:2)
           READ XF1
               AT END MOVE 'E' TO TRC(155:1)
           END-READ
           MOVE XF1-S TO TRC(153:2)
           MOVE XF1-R TO TRC(156:6)
           READ XF1
               AT END MOVE 'E' TO TRC(164:1)
           END-READ
           MOVE XF1-S TO TRC(162:2)
           MOVE XF1-R TO TRC(165:6)
           READ XF1
               AT END MOVE 'E' TO TRC(173:1)
           END-READ
           MOVE XF1-S TO TRC(171:2)
           MOVE XF1-R TO TRC(174:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(180:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(183:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(186:2)
           MOVE 'K01' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(191:1)
           END-READ
           MOVE XF2-S TO TRC(189:2)
           MOVE XF2-R TO TRC(192:8)
           MOVE 'K02' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(202:1)
           END-READ
           MOVE XF2-S TO TRC(200:2)
           MOVE XF2-R TO TRC(203:8)
           MOVE 'K03' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(213:1)
           END-READ
           MOVE XF2-S TO TRC(211:2)
           MOVE XF2-R TO TRC(214:8)
           MOVE 'K04' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(224:1)
           END-READ
           MOVE XF2-S TO TRC(222:2)
           MOVE XF2-R TO TRC(225:8)
           MOVE 'K05' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(235:1)
           END-READ
           MOVE XF2-S TO TRC(233:2)
           MOVE XF2-R TO TRC(236:8)
           MOVE 'K06' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(246:1)
           END-READ
           MOVE XF2-S TO TRC(244:2)
           MOVE XF2-R TO TRC(247:8)
           MOVE 'K07' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(257:1)
           END-READ
           MOVE XF2-S TO TRC(255:2)
           MOVE XF2-R TO TRC(258:8)
           MOVE 'K08' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(268:1)
           END-READ
           MOVE XF2-S TO TRC(266:2)
           MOVE XF2-R TO TRC(269:8)
           MOVE 'A1' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(279:1)
           END-READ
           MOVE XF2-S TO TRC(277:2)
           MOVE XF2-R TO TRC(280:8)
           MOVE 'A2' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(290:1)
           END-READ
           MOVE XF2-S TO TRC(288:2)
           MOVE XF2-R TO TRC(291:8)
           MOVE 'A3' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(301:1)
           END-READ
           MOVE XF2-S TO TRC(299:2)
           MOVE XF2-R TO TRC(302:8)
           MOVE 'A4' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(312:1)
           END-READ
           MOVE XF2-S TO TRC(310:2)
           MOVE XF2-R TO TRC(313:8)
           MOVE 'A5' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(323:1)
           END-READ
           MOVE XF2-S TO TRC(321:2)
           MOVE XF2-R TO TRC(324:8)
           MOVE 'A6' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(334:1)
           END-READ
           MOVE XF2-S TO TRC(332:2)
           MOVE XF2-R TO TRC(335:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(343:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 385
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
