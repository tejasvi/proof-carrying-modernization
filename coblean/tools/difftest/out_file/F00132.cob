       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00132.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00132_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00132_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF2-K.
           SELECT XF3 ASSIGN TO 'F00132_3.dat'
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
           05  TRC PIC X(330) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(8) VALUE SPACES.
           05  XF3-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 382.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           MOVE 'K08' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(6:1)
           END-READ
           MOVE XF3-S TO TRC(4:2)
           MOVE XF3-R TO TRC(7:8)
           MOVE 'K04ECW' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(17:1)
               NOT INVALID KEY MOVE 'N' TO TRC(17:1)
           END-WRITE
           MOVE XF1-S TO TRC(15:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(18:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(21:2)
           MOVE 'K068H1' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(26:1)
           END-WRITE
           MOVE XF1-S TO TRC(24:2)
           MOVE 'K07GG0' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(29:1)
           END-WRITE
           MOVE XF1-S TO TRC(27:2)
           OPEN OUTPUT XF2
           MOVE '--' TO TRC(30:2)
           MOVE 'K04ZES' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(35:1)
           END-WRITE
           MOVE '--' TO TRC(33:2)
           MOVE 'K07Z69' TO XF1-R
           REWRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(38:1)
               NOT INVALID KEY MOVE 'N' TO TRC(38:1)
           END-REWRITE
           MOVE XF1-S TO TRC(36:2)
           MOVE 'K08TS4' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(41:1)
               NOT INVALID KEY MOVE 'N' TO TRC(41:1)
           END-WRITE
           MOVE XF1-S TO TRC(39:2)
           MOVE 'K02EN8' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(42:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(45:2)
           MOVE 'K01I2Z' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(50:1)
           END-WRITE
           MOVE XF1-S TO TRC(48:2)
           MOVE 'K05A5VWJ' TO XF3-R
           WRITE XF3-R
               INVALID KEY MOVE 'E' TO TRC(53:1)
           END-WRITE
           MOVE XF3-S TO TRC(51:2)
           MOVE 'K082EQ' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(56:1)
           END-WRITE
           MOVE XF1-S TO TRC(54:2)
           MOVE 'K04A58D5' TO XF3-R
           WRITE XF3-R
               INVALID KEY MOVE 'E' TO TRC(59:1)
           END-WRITE
           MOVE XF3-S TO TRC(57:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(60:2)
           OPEN I-O XF3
           MOVE XF3-S TO TRC(63:2)
           MOVE 'K05' TO XF3-K
           DELETE XF3 RECORD
           END-DELETE
           MOVE XF3-S TO TRC(66:2)
           MOVE 'K083SB' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(71:1)
           END-WRITE
           MOVE '--' TO TRC(69:2)
           MOVE 'K05A19XO' TO XF3-R
           REWRITE XF3-R
               NOT INVALID KEY MOVE 'N' TO TRC(74:1)
           END-REWRITE
           MOVE XF3-S TO TRC(72:2)
           MOVE 'K02DGD' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(77:1)
           END-WRITE
           MOVE '--' TO TRC(75:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(78:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(81:2)
           READ XF1
               AT END MOVE 'E' TO TRC(86:1)
           END-READ
           MOVE XF1-S TO TRC(84:2)
           MOVE XF1-R TO TRC(87:6)
           READ XF1
               AT END MOVE 'E' TO TRC(95:1)
           END-READ
           MOVE XF1-S TO TRC(93:2)
           MOVE XF1-R TO TRC(96:6)
           READ XF1
               AT END MOVE 'E' TO TRC(104:1)
           END-READ
           MOVE XF1-S TO TRC(102:2)
           MOVE XF1-R TO TRC(105:6)
           READ XF1
               AT END MOVE 'E' TO TRC(113:1)
           END-READ
           MOVE XF1-S TO TRC(111:2)
           MOVE XF1-R TO TRC(114:6)
           READ XF1
               AT END MOVE 'E' TO TRC(122:1)
           END-READ
           MOVE XF1-S TO TRC(120:2)
           MOVE XF1-R TO TRC(123:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(129:2)
           CLOSE XF2
           MOVE '--' TO TRC(132:2)
           OPEN INPUT XF2
           MOVE '--' TO TRC(135:2)
           READ XF2
               AT END MOVE 'E' TO TRC(140:1)
           END-READ
           MOVE '--' TO TRC(138:2)
           MOVE XF2-R TO TRC(141:6)
           READ XF2
               AT END MOVE 'E' TO TRC(149:1)
           END-READ
           MOVE '--' TO TRC(147:2)
           MOVE XF2-R TO TRC(150:6)
           READ XF2
               AT END MOVE 'E' TO TRC(158:1)
           END-READ
           MOVE '--' TO TRC(156:2)
           MOVE XF2-R TO TRC(159:6)
           CLOSE XF2
           MOVE '--' TO TRC(165:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(168:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(171:2)
           MOVE 'K01' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(176:1)
           END-READ
           MOVE XF3-S TO TRC(174:2)
           MOVE XF3-R TO TRC(177:8)
           MOVE 'K02' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(187:1)
           END-READ
           MOVE XF3-S TO TRC(185:2)
           MOVE XF3-R TO TRC(188:8)
           MOVE 'K03' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(198:1)
           END-READ
           MOVE XF3-S TO TRC(196:2)
           MOVE XF3-R TO TRC(199:8)
           MOVE 'K04' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(209:1)
           END-READ
           MOVE XF3-S TO TRC(207:2)
           MOVE XF3-R TO TRC(210:8)
           MOVE 'K05' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(220:1)
           END-READ
           MOVE XF3-S TO TRC(218:2)
           MOVE XF3-R TO TRC(221:8)
           MOVE 'K06' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(231:1)
           END-READ
           MOVE XF3-S TO TRC(229:2)
           MOVE XF3-R TO TRC(232:8)
           MOVE 'K07' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(242:1)
           END-READ
           MOVE XF3-S TO TRC(240:2)
           MOVE XF3-R TO TRC(243:8)
           MOVE 'K08' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(253:1)
           END-READ
           MOVE XF3-S TO TRC(251:2)
           MOVE XF3-R TO TRC(254:8)
           MOVE 'A1' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(264:1)
           END-READ
           MOVE XF3-S TO TRC(262:2)
           MOVE XF3-R TO TRC(265:8)
           MOVE 'A2' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(275:1)
           END-READ
           MOVE XF3-S TO TRC(273:2)
           MOVE XF3-R TO TRC(276:8)
           MOVE 'A3' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(286:1)
           END-READ
           MOVE XF3-S TO TRC(284:2)
           MOVE XF3-R TO TRC(287:8)
           MOVE 'A4' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(297:1)
           END-READ
           MOVE XF3-S TO TRC(295:2)
           MOVE XF3-R TO TRC(298:8)
           MOVE 'A5' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(308:1)
           END-READ
           MOVE XF3-S TO TRC(306:2)
           MOVE XF3-R TO TRC(309:8)
           MOVE 'A6' TO XF3-A
           READ XF3 KEY IS XF3-A
               INVALID KEY MOVE 'E' TO TRC(319:1)
           END-READ
           MOVE XF3-S TO TRC(317:2)
           MOVE XF3-R TO TRC(320:8)
           CLOSE XF3
           MOVE XF3-S TO TRC(328:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 382
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
