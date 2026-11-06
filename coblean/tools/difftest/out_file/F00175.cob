       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00175.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00175_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00175_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF2-K
               ALTERNATE RECORD KEY IS XF2-A
               FILE STATUS IS XF2-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-D PIC X(3).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-A PIC X(2).
           05  XF2-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(334) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 374.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(4:2)
           MOVE 'K02A1DBU' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(7:2)
           MOVE 'K06A1KYX' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(12:1)
               NOT INVALID KEY MOVE 'N' TO TRC(12:1)
           END-WRITE
           MOVE XF2-S TO TRC(10:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(13:2)
           MOVE 'K07QXT' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(18:1)
           END-WRITE
           MOVE XF1-S TO TRC(16:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(19:2)
           MOVE 'K0156K' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(22:2)
           MOVE 'A4' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(27:1)
               NOT INVALID KEY MOVE 'N' TO TRC(27:1)
           END-READ
           MOVE XF2-S TO TRC(25:2)
           MOVE XF2-R TO TRC(28:8)
           MOVE 'K08A3OPA' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(36:2)
           MOVE 'K083LK' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(41:1)
           END-WRITE
           MOVE XF1-S TO TRC(39:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(42:2)
           MOVE 'K02BZU' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(47:1)
               NOT INVALID KEY MOVE 'N' TO TRC(47:1)
           END-WRITE
           MOVE XF1-S TO TRC(45:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(48:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(51:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(54:2)
           MOVE 'K082YG' TO XF1-R
           REWRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(59:1)
           END-REWRITE
           MOVE XF1-S TO TRC(57:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(60:2)
           READ XF1
               NOT AT END MOVE 'N' TO TRC(65:1)
           END-READ
           MOVE XF1-S TO TRC(63:2)
           MOVE XF1-R TO TRC(66:6)
           MOVE 'K07GIP' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(74:1)
               NOT INVALID KEY MOVE 'N' TO TRC(74:1)
           END-WRITE
           MOVE XF1-S TO TRC(72:2)
           MOVE 'K08' TO XF2-K
           DELETE XF2 RECORD
               NOT INVALID KEY MOVE 'N' TO TRC(77:1)
           END-DELETE
           MOVE XF2-S TO TRC(75:2)
           MOVE 'K05' TO XF2-K
           READ XF2 INTO XF2-I
           END-READ
           MOVE XF2-S TO TRC(78:2)
           MOVE XF2-R TO TRC(81:8)
           MOVE XF2-I TO TRC(89:8)
           MOVE 'K0850Q' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(99:1)
               NOT INVALID KEY MOVE 'N' TO TRC(99:1)
           END-WRITE
           MOVE XF1-S TO TRC(97:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(100:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(103:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(106:2)
           MOVE 'K06A6YB3' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(109:2)
           READ XF1 INTO XF1-I
           END-READ
           MOVE XF1-S TO TRC(112:2)
           MOVE XF1-R TO TRC(115:6)
           MOVE XF1-I TO TRC(121:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(127:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(130:2)
           MOVE 'K08T3A' TO XF1-R
           REWRITE XF1-R
           END-REWRITE
           MOVE XF1-S TO TRC(133:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(136:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(139:2)
           READ XF1
               AT END MOVE 'E' TO TRC(144:1)
           END-READ
           MOVE XF1-S TO TRC(142:2)
           MOVE XF1-R TO TRC(145:6)
           READ XF1
               AT END MOVE 'E' TO TRC(153:1)
           END-READ
           MOVE XF1-S TO TRC(151:2)
           MOVE XF1-R TO TRC(154:6)
           READ XF1
               AT END MOVE 'E' TO TRC(162:1)
           END-READ
           MOVE XF1-S TO TRC(160:2)
           MOVE XF1-R TO TRC(163:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(169:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(172:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(175:2)
           MOVE 'K01' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(180:1)
           END-READ
           MOVE XF2-S TO TRC(178:2)
           MOVE XF2-R TO TRC(181:8)
           MOVE 'K02' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(191:1)
           END-READ
           MOVE XF2-S TO TRC(189:2)
           MOVE XF2-R TO TRC(192:8)
           MOVE 'K03' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(202:1)
           END-READ
           MOVE XF2-S TO TRC(200:2)
           MOVE XF2-R TO TRC(203:8)
           MOVE 'K04' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(213:1)
           END-READ
           MOVE XF2-S TO TRC(211:2)
           MOVE XF2-R TO TRC(214:8)
           MOVE 'K05' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(224:1)
           END-READ
           MOVE XF2-S TO TRC(222:2)
           MOVE XF2-R TO TRC(225:8)
           MOVE 'K06' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(235:1)
           END-READ
           MOVE XF2-S TO TRC(233:2)
           MOVE XF2-R TO TRC(236:8)
           MOVE 'K07' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(246:1)
           END-READ
           MOVE XF2-S TO TRC(244:2)
           MOVE XF2-R TO TRC(247:8)
           MOVE 'K08' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(257:1)
           END-READ
           MOVE XF2-S TO TRC(255:2)
           MOVE XF2-R TO TRC(258:8)
           MOVE 'A1' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(268:1)
           END-READ
           MOVE XF2-S TO TRC(266:2)
           MOVE XF2-R TO TRC(269:8)
           MOVE 'A2' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(279:1)
           END-READ
           MOVE XF2-S TO TRC(277:2)
           MOVE XF2-R TO TRC(280:8)
           MOVE 'A3' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(290:1)
           END-READ
           MOVE XF2-S TO TRC(288:2)
           MOVE XF2-R TO TRC(291:8)
           MOVE 'A4' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(301:1)
           END-READ
           MOVE XF2-S TO TRC(299:2)
           MOVE XF2-R TO TRC(302:8)
           MOVE 'A5' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(312:1)
           END-READ
           MOVE XF2-S TO TRC(310:2)
           MOVE XF2-R TO TRC(313:8)
           MOVE 'A6' TO XF2-A
           READ XF2 KEY IS XF2-A
               INVALID KEY MOVE 'E' TO TRC(323:1)
           END-READ
           MOVE XF2-S TO TRC(321:2)
           MOVE XF2-R TO TRC(324:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(332:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 374
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
