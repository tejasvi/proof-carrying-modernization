       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00077.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00077_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00077_2.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00077_3.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF3-K
               ALTERNATE RECORD KEY IS XF3-A.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
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
           05  TRC PIC X(341) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-I PIC X(8) VALUE SPACES.
           05  XF3-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 393.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           OPEN OUTPUT XF3
           MOVE '--' TO TRC(4:2)
           MOVE '3TY79X' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(7:2)
           MOVE 'FEYHSI' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(10:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(13:2)
           MOVE 'B5XGRS' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(16:2)
           MOVE 'K03A3DTN' TO XF3-R
           WRITE XF3-R
               NOT INVALID KEY MOVE 'N' TO TRC(21:1)
           END-WRITE
           MOVE '--' TO TRC(19:2)
           MOVE '9ICSSZ' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(22:2)
           CLOSE XF3
           MOVE '--' TO TRC(25:2)
           MOVE 'YC3RV8' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(28:2)
           OPEN I-O XF3
           MOVE '--' TO TRC(31:2)
           MOVE 'OE0T1Q' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE XF2-S TO TRC(34:2)
           MOVE 'PFN4WQ' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(37:2)
           MOVE '54S8WV' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(40:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(43:2)
           READ XF2 NEXT RECORD
               AT END MOVE 'E' TO TRC(48:1)
               NOT AT END MOVE 'N' TO TRC(48:1)
           END-READ
           MOVE XF2-S TO TRC(46:2)
           MOVE XF2-R TO TRC(49:6)
           READ XF3
               AT END MOVE 'E' TO TRC(57:1)
           END-READ
           MOVE '--' TO TRC(55:2)
           MOVE XF3-R TO TRC(58:8)
           MOVE 'K03A3QFC' TO XF3-R
           REWRITE XF3-R
               INVALID KEY MOVE 'E' TO TRC(68:1)
           END-REWRITE
           MOVE '--' TO TRC(66:2)
           READ XF3 NEXT RECORD
               AT END MOVE 'E' TO TRC(71:1)
               NOT AT END MOVE 'N' TO TRC(71:1)
           END-READ
           MOVE '--' TO TRC(69:2)
           MOVE XF3-R TO TRC(72:8)
           MOVE 'Q4L4JK' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(80:2)
           READ XF2 NEXT RECORD INTO XF2-I
               NOT AT END MOVE 'N' TO TRC(85:1)
           END-READ
           MOVE XF2-S TO TRC(83:2)
           MOVE XF2-R TO TRC(86:6)
           MOVE XF2-I TO TRC(92:6)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(98:2)
           MOVE '4S7UA9' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(101:2)
           MOVE 'K07WGN' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(106:1)
               NOT INVALID KEY MOVE 'N' TO TRC(106:1)
           END-WRITE
           MOVE XF1-S TO TRC(104:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(107:2)
           MOVE 'CMQJBD' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE XF2-S TO TRC(110:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(113:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(116:2)
           MOVE 'K01' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(121:1)
           END-READ
           MOVE XF1-S TO TRC(119:2)
           MOVE XF1-R TO TRC(122:6)
           MOVE 'K02' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(130:1)
           END-READ
           MOVE XF1-S TO TRC(128:2)
           MOVE XF1-R TO TRC(131:6)
           MOVE 'K03' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(139:1)
           END-READ
           MOVE XF1-S TO TRC(137:2)
           MOVE XF1-R TO TRC(140:6)
           MOVE 'K04' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(148:1)
           END-READ
           MOVE XF1-S TO TRC(146:2)
           MOVE XF1-R TO TRC(149:6)
           MOVE 'K05' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(157:1)
           END-READ
           MOVE XF1-S TO TRC(155:2)
           MOVE XF1-R TO TRC(158:6)
           MOVE 'K06' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(166:1)
           END-READ
           MOVE XF1-S TO TRC(164:2)
           MOVE XF1-R TO TRC(167:6)
           MOVE 'K07' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(175:1)
           END-READ
           MOVE XF1-S TO TRC(173:2)
           MOVE XF1-R TO TRC(176:6)
           MOVE 'K08' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(184:1)
           END-READ
           MOVE XF1-S TO TRC(182:2)
           MOVE XF1-R TO TRC(185:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(191:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(194:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(197:2)
           READ XF2
               AT END MOVE 'E' TO TRC(202:1)
           END-READ
           MOVE XF2-S TO TRC(200:2)
           MOVE XF2-R TO TRC(203:6)
           READ XF2
               AT END MOVE 'E' TO TRC(211:1)
           END-READ
           MOVE XF2-S TO TRC(209:2)
           MOVE XF2-R TO TRC(212:6)
           READ XF2
               AT END MOVE 'E' TO TRC(220:1)
           END-READ
           MOVE XF2-S TO TRC(218:2)
           MOVE XF2-R TO TRC(221:6)
           READ XF2
               AT END MOVE 'E' TO TRC(229:1)
           END-READ
           MOVE XF2-S TO TRC(227:2)
           MOVE XF2-R TO TRC(230:6)
           READ XF2
               AT END MOVE 'E' TO TRC(238:1)
           END-READ
           MOVE XF2-S TO TRC(236:2)
           MOVE XF2-R TO TRC(239:6)
           READ XF2
               AT END MOVE 'E' TO TRC(247:1)
           END-READ
           MOVE XF2-S TO TRC(245:2)
           MOVE XF2-R TO TRC(248:6)
           READ XF2
               AT END MOVE 'E' TO TRC(256:1)
           END-READ
           MOVE XF2-S TO TRC(254:2)
           MOVE XF2-R TO TRC(257:6)
           READ XF2
               AT END MOVE 'E' TO TRC(265:1)
           END-READ
           MOVE XF2-S TO TRC(263:2)
           MOVE XF2-R TO TRC(266:6)
           READ XF2
               AT END MOVE 'E' TO TRC(274:1)
           END-READ
           MOVE XF2-S TO TRC(272:2)
           MOVE XF2-R TO TRC(275:6)
           READ XF2
               AT END MOVE 'E' TO TRC(283:1)
           END-READ
           MOVE XF2-S TO TRC(281:2)
           MOVE XF2-R TO TRC(284:6)
           READ XF2
               AT END MOVE 'E' TO TRC(292:1)
           END-READ
           MOVE XF2-S TO TRC(290:2)
           MOVE XF2-R TO TRC(293:6)
           READ XF2
               AT END MOVE 'E' TO TRC(301:1)
           END-READ
           MOVE XF2-S TO TRC(299:2)
           MOVE XF2-R TO TRC(302:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(308:2)
           CLOSE XF3
           MOVE '--' TO TRC(311:2)
           OPEN INPUT XF3
           MOVE '--' TO TRC(314:2)
           READ XF3
               AT END MOVE 'E' TO TRC(319:1)
           END-READ
           MOVE '--' TO TRC(317:2)
           MOVE XF3-R TO TRC(320:8)
           READ XF3
               AT END MOVE 'E' TO TRC(330:1)
           END-READ
           MOVE '--' TO TRC(328:2)
           MOVE XF3-R TO TRC(331:8)
           CLOSE XF3
           MOVE '--' TO TRC(339:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 393
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
