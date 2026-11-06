       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00010.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00010_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(216) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 238.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           MOVE 'K04JA7' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(6:1)
           END-WRITE
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K04GSO' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(9:1)
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           MOVE 'K07RQT' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(12:1)
           END-WRITE
           MOVE XF1-S TO TRC(10:2)
           MOVE 'K07CCK' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(15:1)
           END-WRITE
           MOVE XF1-S TO TRC(13:2)
           MOVE 'K05ABP' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(16:2)
           MOVE 'K06SFH' TO XF1-R
           REWRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(21:1)
           END-REWRITE
           MOVE XF1-S TO TRC(19:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(22:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(25:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(28:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(31:2)
           MOVE 'K05' TO XF1-K
           READ XF1 KEY IS XF1-K
               INVALID KEY MOVE 'E' TO TRC(36:1)
           END-READ
           MOVE XF1-S TO TRC(34:2)
           MOVE XF1-R TO TRC(37:6)
           MOVE 'K023XE' TO XF1-R
           REWRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(45:1)
           END-REWRITE
           MOVE XF1-S TO TRC(43:2)
           MOVE 'K07T8M' TO XF1-W
           REWRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(48:1)
           END-REWRITE
           MOVE XF1-S TO TRC(46:2)
           MOVE 'K04TCG' TO XF1-W
           REWRITE XF1-R FROM XF1-W
           END-REWRITE
           MOVE XF1-S TO TRC(49:2)
           MOVE 'K04' TO XF1-K
           READ XF1 KEY IS XF1-K
               INVALID KEY MOVE 'E' TO TRC(54:1)
           END-READ
           MOVE XF1-S TO TRC(52:2)
           MOVE XF1-R TO TRC(55:6)
           MOVE 'K04' TO XF1-K
           READ XF1 KEY IS XF1-K
           END-READ
           MOVE XF1-S TO TRC(61:2)
           MOVE XF1-R TO TRC(64:6)
           MOVE 'K05' TO XF1-K
           READ XF1 INTO XF1-I
               NOT INVALID KEY MOVE 'N' TO TRC(72:1)
           END-READ
           MOVE XF1-S TO TRC(70:2)
           MOVE XF1-R TO TRC(73:6)
           MOVE XF1-I TO TRC(79:6)
           MOVE 'K07' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(87:1)
               NOT INVALID KEY MOVE 'N' TO TRC(87:1)
           END-READ
           MOVE XF1-S TO TRC(85:2)
           MOVE XF1-R TO TRC(88:6)
           MOVE 'K04EWX' TO XF1-R
           REWRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(96:1)
           END-REWRITE
           MOVE XF1-S TO TRC(94:2)
           MOVE 'K05' TO XF1-K
           READ XF1 INTO XF1-I
               INVALID KEY MOVE 'E' TO TRC(99:1)
           END-READ
           MOVE XF1-S TO TRC(97:2)
           MOVE XF1-R TO TRC(100:6)
           MOVE XF1-I TO TRC(106:6)
           MOVE 'K08' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(114:1)
           END-READ
           MOVE XF1-S TO TRC(112:2)
           MOVE XF1-R TO TRC(115:6)
           MOVE 'K020NB' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(123:1)
           END-WRITE
           MOVE XF1-S TO TRC(121:2)
           MOVE 'K01' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(126:1)
           END-READ
           MOVE XF1-S TO TRC(124:2)
           MOVE XF1-R TO TRC(127:6)
           MOVE 'K07AIE' TO XF1-W
           WRITE XF1-R FROM XF1-W
               NOT INVALID KEY MOVE 'N' TO TRC(135:1)
           END-WRITE
           MOVE XF1-S TO TRC(133:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(136:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(139:2)
           MOVE 'K01' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(144:1)
           END-READ
           MOVE XF1-S TO TRC(142:2)
           MOVE XF1-R TO TRC(145:6)
           MOVE 'K02' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(153:1)
           END-READ
           MOVE XF1-S TO TRC(151:2)
           MOVE XF1-R TO TRC(154:6)
           MOVE 'K03' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(162:1)
           END-READ
           MOVE XF1-S TO TRC(160:2)
           MOVE XF1-R TO TRC(163:6)
           MOVE 'K04' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(171:1)
           END-READ
           MOVE XF1-S TO TRC(169:2)
           MOVE XF1-R TO TRC(172:6)
           MOVE 'K05' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(180:1)
           END-READ
           MOVE XF1-S TO TRC(178:2)
           MOVE XF1-R TO TRC(181:6)
           MOVE 'K06' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(189:1)
           END-READ
           MOVE XF1-S TO TRC(187:2)
           MOVE XF1-R TO TRC(190:6)
           MOVE 'K07' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(198:1)
           END-READ
           MOVE XF1-S TO TRC(196:2)
           MOVE XF1-R TO TRC(199:6)
           MOVE 'K08' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(207:1)
           END-READ
           MOVE XF1-S TO TRC(205:2)
           MOVE XF1-R TO TRC(208:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(214:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 238
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
