       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00098.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00098_1.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00098_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF2-K
               ALTERNATE RECORD KEY IS XF2-A
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00098_3.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF3-K
               ALTERNATE RECORD KEY IS XF3-A
               FILE STATUS IS XF3-S.
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
       FD  XF3.
       01  XF3-R.
           05  XF3-K PIC X(3).
           05  XF3-A PIC X(2).
           05  XF3-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(244) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(8) VALUE SPACES.
           05  XF3-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 302.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(4:2)
           MOVE 'K08A3WLS' TO XF3-W
           WRITE XF3-R FROM XF3-W
               INVALID KEY MOVE 'E' TO TRC(9:1)
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF3-S TO TRC(7:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(10:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(13:2)
           MOVE 'K02A2NTB' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(18:1)
           END-WRITE
           MOVE XF2-S TO TRC(16:2)
           READ XF3 NEXT RECORD
               AT END MOVE 'E' TO TRC(21:1)
           END-READ
           MOVE XF3-S TO TRC(19:2)
           MOVE XF3-R TO TRC(22:8)
           MOVE 'K08A3RWQ' TO XF3-W
           WRITE XF3-R FROM XF3-W
           END-WRITE
           MOVE XF3-S TO TRC(30:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(33:2)
           MOVE 'K08A3BXM' TO XF3-R
           WRITE XF3-R
               INVALID KEY MOVE 'E' TO TRC(38:1)
               NOT INVALID KEY MOVE 'N' TO TRC(38:1)
           END-WRITE
           MOVE XF3-S TO TRC(36:2)
           MOVE 'K08A21GJ' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(39:2)
           MOVE 'K02A1OBG' TO XF2-R
           WRITE XF2-R
               NOT INVALID KEY MOVE 'N' TO TRC(44:1)
           END-WRITE
           MOVE XF2-S TO TRC(42:2)
           MOVE 'K04A5YTT' TO XF3-R
           WRITE XF3-R
               INVALID KEY MOVE 'E' TO TRC(47:1)
           END-WRITE
           MOVE XF3-S TO TRC(45:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(48:2)
           READ XF3
               AT END MOVE 'E' TO TRC(53:1)
               NOT AT END MOVE 'N' TO TRC(53:1)
           END-READ
           MOVE XF3-S TO TRC(51:2)
           MOVE XF3-R TO TRC(54:8)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(62:2)
           READ XF1
               NOT AT END MOVE 'N' TO TRC(67:1)
           END-READ
           MOVE XF1-S TO TRC(65:2)
           MOVE XF1-R TO TRC(68:6)
           MOVE 'K04A2DFB' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(74:2)
           OPEN I-O XF3
           MOVE XF3-S TO TRC(77:2)
           MOVE 'K05A1Y2L' TO XF3-W
           WRITE XF3-R FROM XF3-W
               NOT INVALID KEY MOVE 'N' TO TRC(82:1)
           END-WRITE
           MOVE XF3-S TO TRC(80:2)
           MOVE 'K06A3J5V' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(85:1)
           END-WRITE
           MOVE XF2-S TO TRC(83:2)
           MOVE 'K08A2RQH' TO XF3-R
           REWRITE XF3-R
               NOT INVALID KEY MOVE 'N' TO TRC(88:1)
           END-REWRITE
           MOVE XF3-S TO TRC(86:2)
           MOVE 'T72945' TO XF1-R
           REWRITE XF1-R
           END-REWRITE
           MOVE XF1-S TO TRC(89:2)
           READ XF1 NEXT RECORD
               AT END MOVE 'E' TO TRC(94:1)
           END-READ
           MOVE XF1-S TO TRC(92:2)
           MOVE XF1-R TO TRC(95:6)
           MOVE '2C119D' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(101:2)
           MOVE 'K08A4V4Y' TO XF3-W
           WRITE XF3-R FROM XF3-W
               INVALID KEY MOVE 'E' TO TRC(106:1)
           END-WRITE
           MOVE XF3-S TO TRC(104:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(107:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(110:2)
           READ XF2
               AT END MOVE 'E' TO TRC(115:1)
               NOT AT END MOVE 'N' TO TRC(115:1)
           END-READ
           MOVE XF2-S TO TRC(113:2)
           MOVE XF2-R TO TRC(116:8)
           READ XF3
               AT END MOVE 'E' TO TRC(126:1)
           END-READ
           MOVE XF3-S TO TRC(124:2)
           MOVE XF3-R TO TRC(127:8)
           READ XF3 INTO XF3-I
               AT END MOVE 'E' TO TRC(137:1)
               NOT AT END MOVE 'N' TO TRC(137:1)
           END-READ
           MOVE XF3-S TO TRC(135:2)
           MOVE XF3-R TO TRC(138:8)
           MOVE XF3-I TO TRC(146:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(154:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(157:2)
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
           READ XF2
               AT END MOVE 'E' TO TRC(180:1)
           END-READ
           MOVE XF2-S TO TRC(178:2)
           MOVE XF2-R TO TRC(181:8)
           READ XF2
               AT END MOVE 'E' TO TRC(191:1)
           END-READ
           MOVE XF2-S TO TRC(189:2)
           MOVE XF2-R TO TRC(192:8)
           READ XF2
               AT END MOVE 'E' TO TRC(202:1)
           END-READ
           MOVE XF2-S TO TRC(200:2)
           MOVE XF2-R TO TRC(203:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(211:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(214:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(217:2)
           READ XF3
               AT END MOVE 'E' TO TRC(222:1)
           END-READ
           MOVE XF3-S TO TRC(220:2)
           MOVE XF3-R TO TRC(223:8)
           READ XF3
               AT END MOVE 'E' TO TRC(233:1)
           END-READ
           MOVE XF3-S TO TRC(231:2)
           MOVE XF3-R TO TRC(234:8)
           CLOSE XF3
           MOVE XF3-S TO TRC(242:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 302
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
