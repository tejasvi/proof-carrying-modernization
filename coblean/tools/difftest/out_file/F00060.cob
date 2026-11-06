       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00060.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00060_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00060_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF2-K
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00060_3.dat'
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
           05  XF1-D PIC X(3).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-D PIC X(3).
       FD  XF3.
       01  XF3-R.
           05  XF3-K PIC X(3).
           05  XF3-A PIC X(2).
           05  XF3-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(360) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(8) VALUE SPACES.
           05  XF3-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 414.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(4:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(7:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(10:2)
           MOVE 'K06WWC' TO XF2-W
           REWRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(15:1)
           END-REWRITE
           MOVE XF2-S TO TRC(13:2)
           MOVE 'K03A6D2E' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(16:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(19:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(22:2)
           MOVE 'K04' TO XF2-K
           READ XF2 KEY IS XF2-K
               INVALID KEY MOVE 'E' TO TRC(27:1)
           END-READ
           MOVE XF2-S TO TRC(25:2)
           MOVE XF2-R TO TRC(28:6)
           MOVE 'K03' TO XF2-K
           DELETE XF2 RECORD
               INVALID KEY MOVE 'E' TO TRC(36:1)
               NOT INVALID KEY MOVE 'N' TO TRC(36:1)
           END-DELETE
           MOVE XF2-S TO TRC(34:2)
           MOVE 'A3' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(39:1)
               NOT INVALID KEY MOVE 'N' TO TRC(39:1)
           END-READ
           MOVE XF3-S TO TRC(37:2)
           MOVE XF3-R TO TRC(40:8)
           MOVE 'K05NGW' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(50:1)
               NOT INVALID KEY MOVE 'N' TO TRC(50:1)
           END-WRITE
           MOVE XF1-S TO TRC(48:2)
           MOVE 'K08' TO XF2-K
           DELETE XF2 RECORD
               INVALID KEY MOVE 'E' TO TRC(53:1)
           END-DELETE
           MOVE XF2-S TO TRC(51:2)
           MOVE 'K06W3G' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(56:1)
               NOT INVALID KEY MOVE 'N' TO TRC(56:1)
           END-WRITE
           MOVE XF1-S TO TRC(54:2)
           MOVE 'K08' TO XF2-K
           READ XF2 INTO XF2-I
               NOT INVALID KEY MOVE 'N' TO TRC(59:1)
           END-READ
           MOVE XF2-S TO TRC(57:2)
           MOVE XF2-R TO TRC(60:6)
           MOVE XF2-I TO TRC(66:6)
           MOVE 'K0827W' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(72:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(75:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(78:2)
           READ XF1
               AT END MOVE 'E' TO TRC(83:1)
           END-READ
           MOVE XF1-S TO TRC(81:2)
           MOVE XF1-R TO TRC(84:6)
           READ XF1
               AT END MOVE 'E' TO TRC(92:1)
           END-READ
           MOVE XF1-S TO TRC(90:2)
           MOVE XF1-R TO TRC(93:6)
           READ XF1
               AT END MOVE 'E' TO TRC(101:1)
           END-READ
           MOVE XF1-S TO TRC(99:2)
           MOVE XF1-R TO TRC(102:6)
           READ XF1
               AT END MOVE 'E' TO TRC(110:1)
           END-READ
           MOVE XF1-S TO TRC(108:2)
           MOVE XF1-R TO TRC(111:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(117:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(120:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(123:2)
           MOVE 'K01' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(128:1)
           END-READ
           MOVE XF2-S TO TRC(126:2)
           MOVE XF2-R TO TRC(129:6)
           MOVE 'K02' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(137:1)
           END-READ
           MOVE XF2-S TO TRC(135:2)
           MOVE XF2-R TO TRC(138:6)
           MOVE 'K03' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(146:1)
           END-READ
           MOVE XF2-S TO TRC(144:2)
           MOVE XF2-R TO TRC(147:6)
           MOVE 'K04' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(155:1)
           END-READ
           MOVE XF2-S TO TRC(153:2)
           MOVE XF2-R TO TRC(156:6)
           MOVE 'K05' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(164:1)
           END-READ
           MOVE XF2-S TO TRC(162:2)
           MOVE XF2-R TO TRC(165:6)
           MOVE 'K06' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(173:1)
           END-READ
           MOVE XF2-S TO TRC(171:2)
           MOVE XF2-R TO TRC(174:6)
           MOVE 'K07' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(182:1)
           END-READ
           MOVE XF2-S TO TRC(180:2)
           MOVE XF2-R TO TRC(183:6)
           MOVE 'K08' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(191:1)
           END-READ
           MOVE XF2-S TO TRC(189:2)
           MOVE XF2-R TO TRC(192:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(198:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(201:2)
           MOVE 'K01' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(206:1)
           END-READ
           MOVE XF3-S TO TRC(204:2)
           MOVE XF3-R TO TRC(207:8)
           MOVE 'K02' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(217:1)
           END-READ
           MOVE XF3-S TO TRC(215:2)
           MOVE XF3-R TO TRC(218:8)
           MOVE 'K03' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(228:1)
           END-READ
           MOVE XF3-S TO TRC(226:2)
           MOVE XF3-R TO TRC(229:8)
           MOVE 'K04' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(239:1)
           END-READ
           MOVE XF3-S TO TRC(237:2)
           MOVE XF3-R TO TRC(240:8)
           MOVE 'K05' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(250:1)
           END-READ
           MOVE XF3-S TO TRC(248:2)
           MOVE XF3-R TO TRC(251:8)
           MOVE 'K06' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(261:1)
           END-READ
           MOVE XF3-S TO TRC(259:2)
           MOVE XF3-R TO TRC(262:8)
           MOVE 'K07' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(272:1)
           END-READ
           MOVE XF3-S TO TRC(270:2)
           MOVE XF3-R TO TRC(273:8)
           MOVE 'K08' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(283:1)
           END-READ
           MOVE XF3-S TO TRC(281:2)
           MOVE XF3-R TO TRC(284:8)
           MOVE 'A1' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(294:1)
           END-READ
           MOVE XF3-S TO TRC(292:2)
           MOVE XF3-R TO TRC(295:8)
           MOVE 'A2' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(305:1)
           END-READ
           MOVE XF3-S TO TRC(303:2)
           MOVE XF3-R TO TRC(306:8)
           MOVE 'A3' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(316:1)
           END-READ
           MOVE XF3-S TO TRC(314:2)
           MOVE XF3-R TO TRC(317:8)
           MOVE 'A4' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(327:1)
           END-READ
           MOVE XF3-S TO TRC(325:2)
           MOVE XF3-R TO TRC(328:8)
           MOVE 'A5' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(338:1)
           END-READ
           MOVE XF3-S TO TRC(336:2)
           MOVE XF3-R TO TRC(339:8)
           MOVE 'A6' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(349:1)
           END-READ
           MOVE XF3-S TO TRC(347:2)
           MOVE XF3-R TO TRC(350:8)
           CLOSE XF3
           MOVE XF3-S TO TRC(358:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 414
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
