       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00013.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00013_1.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00013_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF2-K
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00013_3.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF3-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-D PIC X(6).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-D PIC X(3).
       FD  XF3.
       01  XF3-R.
           05  XF3-D PIC X(6).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(327) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(6) VALUE SPACES.
           05  XF3-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 377.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           CLOSE XF3
           MOVE XF3-S TO TRC(1:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(4:2)
           MOVE 'K06EM0' TO XF2-R
           WRITE XF2-R
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF2-S TO TRC(7:2)
           MOVE 'K05G6Y' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(12:1)
           END-WRITE
           MOVE XF2-S TO TRC(10:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(13:2)
           MOVE 'K06' TO XF2-K
           DELETE XF2 RECORD
           END-DELETE
           MOVE XF2-S TO TRC(16:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(19:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(22:2)
           READ XF3 INTO XF3-I
           END-READ
           MOVE XF3-S TO TRC(25:2)
           MOVE XF3-R TO TRC(28:6)
           MOVE XF3-I TO TRC(34:6)
           CLOSE XF3
           MOVE XF3-S TO TRC(40:2)
           READ XF3
               AT END MOVE 'E' TO TRC(45:1)
           END-READ
           MOVE XF3-S TO TRC(43:2)
           MOVE XF3-R TO TRC(46:6)
           MOVE 'F5MBM5' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(52:2)
           MOVE 'HQX3CP' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(55:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(58:2)
           MOVE 'WSXA1D' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(61:2)
           MOVE '3VVRXC' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(64:2)
           MOVE 'K06' TO XF2-K
           READ XF2 KEY IS XF2-K
           END-READ
           MOVE XF2-S TO TRC(67:2)
           MOVE XF2-R TO TRC(70:6)
           MOVE 'K03MH0' TO XF2-R
           REWRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(78:1)
           END-REWRITE
           MOVE XF2-S TO TRC(76:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(79:2)
           MOVE 'SRF3DH' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(82:2)
           MOVE 'K025Z9' TO XF2-R
           REWRITE XF2-R
           END-REWRITE
           MOVE XF2-S TO TRC(85:2)
           MOVE 'OEWFPT' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(88:2)
           MOVE '06LCTY' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(91:2)
           MOVE 'PCNGRH' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(94:2)
           MOVE 'K06' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(99:1)
               NOT INVALID KEY MOVE 'N' TO TRC(99:1)
           END-READ
           MOVE XF2-S TO TRC(97:2)
           MOVE XF2-R TO TRC(100:6)
           MOVE 'K05' TO XF2-K
           DELETE XF2 RECORD
               INVALID KEY MOVE 'E' TO TRC(108:1)
           END-DELETE
           MOVE XF2-S TO TRC(106:2)
           MOVE 'TC3VL9' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(109:2)
           MOVE 'BT99SZ' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(112:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(115:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(118:2)
           MOVE 'D82O0K' TO XF3-R
           REWRITE XF3-R
           END-REWRITE
           MOVE XF3-S TO TRC(121:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(124:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(127:2)
           READ XF1
               AT END MOVE 'E' TO TRC(132:1)
           END-READ
           MOVE XF1-S TO TRC(130:2)
           MOVE XF1-R TO TRC(133:6)
           READ XF1
               AT END MOVE 'E' TO TRC(141:1)
           END-READ
           MOVE XF1-S TO TRC(139:2)
           MOVE XF1-R TO TRC(142:6)
           READ XF1
               AT END MOVE 'E' TO TRC(150:1)
           END-READ
           MOVE XF1-S TO TRC(148:2)
           MOVE XF1-R TO TRC(151:6)
           READ XF1
               AT END MOVE 'E' TO TRC(159:1)
           END-READ
           MOVE XF1-S TO TRC(157:2)
           MOVE XF1-R TO TRC(160:6)
           READ XF1
               AT END MOVE 'E' TO TRC(168:1)
           END-READ
           MOVE XF1-S TO TRC(166:2)
           MOVE XF1-R TO TRC(169:6)
           READ XF1
               AT END MOVE 'E' TO TRC(177:1)
           END-READ
           MOVE XF1-S TO TRC(175:2)
           MOVE XF1-R TO TRC(178:6)
           READ XF1
               AT END MOVE 'E' TO TRC(186:1)
           END-READ
           MOVE XF1-S TO TRC(184:2)
           MOVE XF1-R TO TRC(187:6)
           READ XF1
               AT END MOVE 'E' TO TRC(195:1)
           END-READ
           MOVE XF1-S TO TRC(193:2)
           MOVE XF1-R TO TRC(196:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(202:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(205:2)
           MOVE 'K01' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(210:1)
           END-READ
           MOVE XF2-S TO TRC(208:2)
           MOVE XF2-R TO TRC(211:6)
           MOVE 'K02' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(219:1)
           END-READ
           MOVE XF2-S TO TRC(217:2)
           MOVE XF2-R TO TRC(220:6)
           MOVE 'K03' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(228:1)
           END-READ
           MOVE XF2-S TO TRC(226:2)
           MOVE XF2-R TO TRC(229:6)
           MOVE 'K04' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(237:1)
           END-READ
           MOVE XF2-S TO TRC(235:2)
           MOVE XF2-R TO TRC(238:6)
           MOVE 'K05' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(246:1)
           END-READ
           MOVE XF2-S TO TRC(244:2)
           MOVE XF2-R TO TRC(247:6)
           MOVE 'K06' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(255:1)
           END-READ
           MOVE XF2-S TO TRC(253:2)
           MOVE XF2-R TO TRC(256:6)
           MOVE 'K07' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(264:1)
           END-READ
           MOVE XF2-S TO TRC(262:2)
           MOVE XF2-R TO TRC(265:6)
           MOVE 'K08' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(273:1)
           END-READ
           MOVE XF2-S TO TRC(271:2)
           MOVE XF2-R TO TRC(274:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(280:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(283:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(286:2)
           READ XF3
               AT END MOVE 'E' TO TRC(291:1)
           END-READ
           MOVE XF3-S TO TRC(289:2)
           MOVE XF3-R TO TRC(292:6)
           READ XF3
               AT END MOVE 'E' TO TRC(300:1)
           END-READ
           MOVE XF3-S TO TRC(298:2)
           MOVE XF3-R TO TRC(301:6)
           READ XF3
               AT END MOVE 'E' TO TRC(309:1)
           END-READ
           MOVE XF3-S TO TRC(307:2)
           MOVE XF3-R TO TRC(310:6)
           READ XF3
               AT END MOVE 'E' TO TRC(318:1)
           END-READ
           MOVE XF3-S TO TRC(316:2)
           MOVE XF3-R TO TRC(319:6)
           CLOSE XF3
           MOVE XF3-S TO TRC(325:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 377
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
