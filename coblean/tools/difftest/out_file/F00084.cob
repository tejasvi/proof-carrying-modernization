       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00084.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00084_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00084_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
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
           05  TRC PIC X(241) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 281.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           MOVE 'K01WOL' TO XF1-R
           REWRITE XF1-R
           END-REWRITE
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K08A5J1Q' TO XF2-W
           WRITE XF2-R FROM XF2-W
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF2-S TO TRC(7:2)
           MOVE 'K02A50OL' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(10:2)
           MOVE 'K05' TO XF1-K
           DELETE XF1 RECORD
               NOT INVALID KEY MOVE 'N' TO TRC(15:1)
           END-DELETE
           MOVE XF1-S TO TRC(13:2)
           MOVE 'K07A4XZT' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(18:1)
               NOT INVALID KEY MOVE 'N' TO TRC(18:1)
           END-WRITE
           MOVE XF2-S TO TRC(16:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(19:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(22:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(25:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(28:2)
           MOVE 'K07VKT' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(31:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(34:2)
           MOVE 'K04CLT' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(39:1)
           END-WRITE
           MOVE XF1-S TO TRC(37:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(40:2)
           READ XF2
           END-READ
           MOVE XF2-S TO TRC(43:2)
           MOVE XF2-R TO TRC(46:8)
           MOVE 'K015NI' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(56:1)
               NOT INVALID KEY MOVE 'N' TO TRC(56:1)
           END-WRITE
           MOVE XF1-S TO TRC(54:2)
           READ XF2 INTO XF2-I
               AT END MOVE 'E' TO TRC(59:1)
               NOT AT END MOVE 'N' TO TRC(59:1)
           END-READ
           MOVE XF2-S TO TRC(57:2)
           MOVE XF2-R TO TRC(60:8)
           MOVE XF2-I TO TRC(68:8)
           READ XF2 NEXT RECORD
               AT END MOVE 'E' TO TRC(78:1)
           END-READ
           MOVE XF2-S TO TRC(76:2)
           MOVE XF2-R TO TRC(79:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(87:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(90:2)
           READ XF2
               NOT AT END MOVE 'N' TO TRC(95:1)
           END-READ
           MOVE XF2-S TO TRC(93:2)
           MOVE XF2-R TO TRC(96:8)
           MOVE 'K04DYL' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(104:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(107:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(110:2)
           READ XF2
               NOT AT END MOVE 'N' TO TRC(115:1)
           END-READ
           MOVE XF2-S TO TRC(113:2)
           MOVE XF2-R TO TRC(116:8)
           MOVE 'K04J18' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(126:1)
           END-WRITE
           MOVE XF1-S TO TRC(124:2)
           MOVE 'K08A5QEF' TO XF2-R
           REWRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(129:1)
               NOT INVALID KEY MOVE 'N' TO TRC(129:1)
           END-REWRITE
           MOVE XF2-S TO TRC(127:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(130:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(133:2)
           MOVE 'K01' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(138:1)
           END-READ
           MOVE XF1-S TO TRC(136:2)
           MOVE XF1-R TO TRC(139:6)
           MOVE 'K02' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(147:1)
           END-READ
           MOVE XF1-S TO TRC(145:2)
           MOVE XF1-R TO TRC(148:6)
           MOVE 'K03' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(156:1)
           END-READ
           MOVE XF1-S TO TRC(154:2)
           MOVE XF1-R TO TRC(157:6)
           MOVE 'K04' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(165:1)
           END-READ
           MOVE XF1-S TO TRC(163:2)
           MOVE XF1-R TO TRC(166:6)
           MOVE 'K05' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(174:1)
           END-READ
           MOVE XF1-S TO TRC(172:2)
           MOVE XF1-R TO TRC(175:6)
           MOVE 'K06' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(183:1)
           END-READ
           MOVE XF1-S TO TRC(181:2)
           MOVE XF1-R TO TRC(184:6)
           MOVE 'K07' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(192:1)
           END-READ
           MOVE XF1-S TO TRC(190:2)
           MOVE XF1-R TO TRC(193:6)
           MOVE 'K08' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(201:1)
           END-READ
           MOVE XF1-S TO TRC(199:2)
           MOVE XF1-R TO TRC(202:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(208:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(211:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(214:2)
           READ XF2
               AT END MOVE 'E' TO TRC(219:1)
           END-READ
           MOVE XF2-S TO TRC(217:2)
           MOVE XF2-R TO TRC(220:8)
           READ XF2
               AT END MOVE 'E' TO TRC(230:1)
           END-READ
           MOVE XF2-S TO TRC(228:2)
           MOVE XF2-R TO TRC(231:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(239:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 281
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
