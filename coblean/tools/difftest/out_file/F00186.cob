       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00186.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00186_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00186_2.dat'
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
           05  XF1-A PIC X(2).
           05  XF1-D PIC X(3).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-A PIC X(2).
           05  XF2-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(275) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 319.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE 'K04A6KKF' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(3:1)
               NOT INVALID KEY MOVE 'N' TO TRC(3:1)
           END-WRITE
           MOVE XF1-S TO TRC(1:2)
           MOVE 'K02' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(6:1)
               NOT INVALID KEY MOVE 'N' TO TRC(6:1)
           END-READ
           MOVE XF1-S TO TRC(4:2)
           MOVE XF1-R TO TRC(7:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(15:2)
           READ XF2
               AT END MOVE 'E' TO TRC(20:1)
           END-READ
           MOVE XF2-S TO TRC(18:2)
           MOVE XF2-R TO TRC(21:8)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(29:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(32:2)
           MOVE 'K04A2QVU' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(37:1)
               NOT INVALID KEY MOVE 'N' TO TRC(37:1)
           END-WRITE
           MOVE XF2-S TO TRC(35:2)
           MOVE 'K05A2WQM' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(38:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(41:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(44:2)
           MOVE 'K04A1EFQ' TO XF2-W
           REWRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(49:1)
               NOT INVALID KEY MOVE 'N' TO TRC(49:1)
           END-REWRITE
           MOVE XF2-S TO TRC(47:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(50:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(53:2)
           MOVE 'K02A2X9Q' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(58:1)
           END-WRITE
           MOVE XF2-S TO TRC(56:2)
           MOVE 'K06A2TXK' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(61:1)
               NOT INVALID KEY MOVE 'N' TO TRC(61:1)
           END-WRITE
           MOVE XF2-S TO TRC(59:2)
           MOVE 'K01A6PQ5' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(64:1)
           END-WRITE
           MOVE XF2-S TO TRC(62:2)
           MOVE 'K03A2RS2' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(65:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(68:2)
           READ XF2
               AT END MOVE 'E' TO TRC(73:1)
           END-READ
           MOVE XF2-S TO TRC(71:2)
           MOVE XF2-R TO TRC(74:8)
           MOVE 'K05A14BI' TO XF1-W
           WRITE XF1-R FROM XF1-W
               NOT INVALID KEY MOVE 'N' TO TRC(84:1)
           END-WRITE
           MOVE XF1-S TO TRC(82:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(85:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(88:2)
           MOVE 'K01' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(93:1)
           END-READ
           MOVE XF1-S TO TRC(91:2)
           MOVE XF1-R TO TRC(94:8)
           MOVE 'K02' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(104:1)
           END-READ
           MOVE XF1-S TO TRC(102:2)
           MOVE XF1-R TO TRC(105:8)
           MOVE 'K03' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(115:1)
           END-READ
           MOVE XF1-S TO TRC(113:2)
           MOVE XF1-R TO TRC(116:8)
           MOVE 'K04' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(126:1)
           END-READ
           MOVE XF1-S TO TRC(124:2)
           MOVE XF1-R TO TRC(127:8)
           MOVE 'K05' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(137:1)
           END-READ
           MOVE XF1-S TO TRC(135:2)
           MOVE XF1-R TO TRC(138:8)
           MOVE 'K06' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(148:1)
           END-READ
           MOVE XF1-S TO TRC(146:2)
           MOVE XF1-R TO TRC(149:8)
           MOVE 'K07' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(159:1)
           END-READ
           MOVE XF1-S TO TRC(157:2)
           MOVE XF1-R TO TRC(160:8)
           MOVE 'K08' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(170:1)
           END-READ
           MOVE XF1-S TO TRC(168:2)
           MOVE XF1-R TO TRC(171:8)
           MOVE 'A1' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(181:1)
           END-READ
           MOVE XF1-S TO TRC(179:2)
           MOVE XF1-R TO TRC(182:8)
           MOVE 'A2' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(192:1)
           END-READ
           MOVE XF1-S TO TRC(190:2)
           MOVE XF1-R TO TRC(193:8)
           MOVE 'A3' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(203:1)
           END-READ
           MOVE XF1-S TO TRC(201:2)
           MOVE XF1-R TO TRC(204:8)
           MOVE 'A4' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(214:1)
           END-READ
           MOVE XF1-S TO TRC(212:2)
           MOVE XF1-R TO TRC(215:8)
           MOVE 'A5' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(225:1)
           END-READ
           MOVE XF1-S TO TRC(223:2)
           MOVE XF1-R TO TRC(226:8)
           MOVE 'A6' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(236:1)
           END-READ
           MOVE XF1-S TO TRC(234:2)
           MOVE XF1-R TO TRC(237:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(245:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(248:2)
           READ XF2
               AT END MOVE 'E' TO TRC(253:1)
           END-READ
           MOVE XF2-S TO TRC(251:2)
           MOVE XF2-R TO TRC(254:8)
           READ XF2
               AT END MOVE 'E' TO TRC(264:1)
           END-READ
           MOVE XF2-S TO TRC(262:2)
           MOVE XF2-R TO TRC(265:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(273:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 319
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
