       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00047.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00047_1.dat'
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
           05  TRC PIC X(195) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 217.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           MOVE 'K08Z8I' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K08D6I' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(9:1)
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           MOVE 'K08M7R' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(10:2)
           MOVE 'K08' TO XF1-K
           READ XF1 KEY IS XF1-K
           END-READ
           MOVE XF1-S TO TRC(13:2)
           MOVE XF1-R TO TRC(16:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(22:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(25:2)
           MOVE 'K07NK1' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(28:2)
           MOVE 'K08GMV' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(31:2)
           MOVE 'K08EXP' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(36:1)
           END-WRITE
           MOVE XF1-S TO TRC(34:2)
           MOVE 'K08P0T' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(39:1)
               NOT INVALID KEY MOVE 'N' TO TRC(39:1)
           END-WRITE
           MOVE XF1-S TO TRC(37:2)
           MOVE 'K04MCM' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(42:1)
           END-WRITE
           MOVE XF1-S TO TRC(40:2)
           MOVE 'K0492I' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(43:2)
           MOVE 'K08OSS' TO XF1-W
           REWRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(48:1)
               NOT INVALID KEY MOVE 'N' TO TRC(48:1)
           END-REWRITE
           MOVE XF1-S TO TRC(46:2)
           MOVE 'K05RCU' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(51:1)
           END-WRITE
           MOVE XF1-S TO TRC(49:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(52:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(55:2)
           MOVE 'K02X47' TO XF1-R
           REWRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(60:1)
           END-REWRITE
           MOVE XF1-S TO TRC(58:2)
           MOVE 'K07' TO XF1-K
           DELETE XF1 RECORD
               INVALID KEY MOVE 'E' TO TRC(63:1)
           END-DELETE
           MOVE XF1-S TO TRC(61:2)
           MOVE 'K08' TO XF1-K
           READ XF1 INTO XF1-I KEY IS XF1-K
               INVALID KEY MOVE 'E' TO TRC(66:1)
           END-READ
           MOVE XF1-S TO TRC(64:2)
           MOVE XF1-R TO TRC(67:6)
           MOVE XF1-I TO TRC(73:6)
           MOVE 'K08' TO XF1-K
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(79:2)
           MOVE 'K05' TO XF1-K
           READ XF1 KEY IS XF1-K
               NOT INVALID KEY MOVE 'N' TO TRC(84:1)
           END-READ
           MOVE XF1-S TO TRC(82:2)
           MOVE XF1-R TO TRC(85:6)
           MOVE 'K01DQM' TO XF1-R
           REWRITE XF1-R
           END-REWRITE
           MOVE XF1-S TO TRC(91:2)
           MOVE 'K05PCK' TO XF1-W
           REWRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(96:1)
               NOT INVALID KEY MOVE 'N' TO TRC(96:1)
           END-REWRITE
           MOVE XF1-S TO TRC(94:2)
           MOVE 'K073Z5' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(99:1)
           END-WRITE
           MOVE XF1-S TO TRC(97:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(100:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(103:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(106:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(109:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(112:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(115:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(118:2)
           MOVE 'K01' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(123:1)
           END-READ
           MOVE XF1-S TO TRC(121:2)
           MOVE XF1-R TO TRC(124:6)
           MOVE 'K02' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(132:1)
           END-READ
           MOVE XF1-S TO TRC(130:2)
           MOVE XF1-R TO TRC(133:6)
           MOVE 'K03' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(141:1)
           END-READ
           MOVE XF1-S TO TRC(139:2)
           MOVE XF1-R TO TRC(142:6)
           MOVE 'K04' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(150:1)
           END-READ
           MOVE XF1-S TO TRC(148:2)
           MOVE XF1-R TO TRC(151:6)
           MOVE 'K05' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(159:1)
           END-READ
           MOVE XF1-S TO TRC(157:2)
           MOVE XF1-R TO TRC(160:6)
           MOVE 'K06' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(168:1)
           END-READ
           MOVE XF1-S TO TRC(166:2)
           MOVE XF1-R TO TRC(169:6)
           MOVE 'K07' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(177:1)
           END-READ
           MOVE XF1-S TO TRC(175:2)
           MOVE XF1-R TO TRC(178:6)
           MOVE 'K08' TO XF1-K
           READ XF1
               INVALID KEY MOVE 'E' TO TRC(186:1)
           END-READ
           MOVE XF1-S TO TRC(184:2)
           MOVE XF1-R TO TRC(187:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(193:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 217
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
