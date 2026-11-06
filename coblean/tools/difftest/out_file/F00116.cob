       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00116.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00116_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-A PIC X(2).
           05  XF1-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(227) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 253.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           MOVE 'K04' TO XF1-K
           READ XF1 INTO XF1-I KEY IS XF1-K
               INVALID KEY MOVE 'E' TO TRC(6:1)
           END-READ
           MOVE XF1-S TO TRC(4:2)
           MOVE XF1-R TO TRC(7:8)
           MOVE XF1-I TO TRC(15:8)
           MOVE 'K06A5MIO' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(25:1)
           END-WRITE
           MOVE XF1-S TO TRC(23:2)
           MOVE 'K08A44PA' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(28:1)
           END-WRITE
           MOVE XF1-S TO TRC(26:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(29:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(32:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(35:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(38:2)
           MOVE 'K07A1GO4' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(43:1)
           END-WRITE
           MOVE XF1-S TO TRC(41:2)
           MOVE 'K07A2D20' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(46:1)
           END-WRITE
           MOVE XF1-S TO TRC(44:2)
           MOVE 'K06A48KN' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(49:1)
               NOT INVALID KEY MOVE 'N' TO TRC(49:1)
           END-WRITE
           MOVE XF1-S TO TRC(47:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(50:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(53:2)
           MOVE 'K06' TO XF1-K
           DELETE XF1 RECORD
               INVALID KEY MOVE 'E' TO TRC(58:1)
           END-DELETE
           MOVE XF1-S TO TRC(56:2)
           MOVE 'K01A5U1E' TO XF1-R
           REWRITE XF1-R
           END-REWRITE
           MOVE XF1-S TO TRC(59:2)
           MOVE 'K07A2JCK' TO XF1-W
           REWRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(64:1)
               NOT INVALID KEY MOVE 'N' TO TRC(64:1)
           END-REWRITE
           MOVE XF1-S TO TRC(62:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(65:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(68:2)
           MOVE 'K01' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(73:1)
           END-READ
           MOVE XF1-S TO TRC(71:2)
           MOVE XF1-R TO TRC(74:8)
           MOVE 'K02' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(84:1)
           END-READ
           MOVE XF1-S TO TRC(82:2)
           MOVE XF1-R TO TRC(85:8)
           MOVE 'K03' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(95:1)
           END-READ
           MOVE XF1-S TO TRC(93:2)
           MOVE XF1-R TO TRC(96:8)
           MOVE 'K04' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(106:1)
           END-READ
           MOVE XF1-S TO TRC(104:2)
           MOVE XF1-R TO TRC(107:8)
           MOVE 'K05' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(117:1)
           END-READ
           MOVE XF1-S TO TRC(115:2)
           MOVE XF1-R TO TRC(118:8)
           MOVE 'K06' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(128:1)
           END-READ
           MOVE XF1-S TO TRC(126:2)
           MOVE XF1-R TO TRC(129:8)
           MOVE 'K07' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(139:1)
           END-READ
           MOVE XF1-S TO TRC(137:2)
           MOVE XF1-R TO TRC(140:8)
           MOVE 'K08' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(150:1)
           END-READ
           MOVE XF1-S TO TRC(148:2)
           MOVE XF1-R TO TRC(151:8)
           MOVE 'A1' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(161:1)
           END-READ
           MOVE XF1-S TO TRC(159:2)
           MOVE XF1-R TO TRC(162:8)
           MOVE 'A2' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(172:1)
           END-READ
           MOVE XF1-S TO TRC(170:2)
           MOVE XF1-R TO TRC(173:8)
           MOVE 'A3' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(183:1)
           END-READ
           MOVE XF1-S TO TRC(181:2)
           MOVE XF1-R TO TRC(184:8)
           MOVE 'A4' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(194:1)
           END-READ
           MOVE XF1-S TO TRC(192:2)
           MOVE XF1-R TO TRC(195:8)
           MOVE 'A5' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(205:1)
           END-READ
           MOVE XF1-S TO TRC(203:2)
           MOVE XF1-R TO TRC(206:8)
           MOVE 'A6' TO XF1-A
           READ XF1 KEY IS XF1-A
               INVALID KEY MOVE 'E' TO TRC(216:1)
           END-READ
           MOVE XF1-S TO TRC(214:2)
           MOVE XF1-R TO TRC(217:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(225:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 253
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
