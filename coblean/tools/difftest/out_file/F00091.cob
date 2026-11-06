       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00091.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00091_1.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF1-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-D PIC X(6).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(240) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 262.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           MOVE '644YCU' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(4:2)
           MOVE '4WDD3O' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           MOVE '4YBPOP' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(10:2)
           MOVE 'XVDJM2' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(13:2)
           MOVE 'BO1U2J' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(16:2)
           MOVE 'G2UX7B' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(19:2)
           MOVE 'RWYCRF' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(22:2)
           READ XF1
           END-READ
           MOVE XF1-S TO TRC(25:2)
           MOVE XF1-R TO TRC(28:6)
           MOVE 'MU8ELH' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(34:2)
           MOVE '2QXN80' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(37:2)
           MOVE '9XDEX1' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(40:2)
           MOVE 'K948UL' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(43:2)
           MOVE '6S883X' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(46:2)
           MOVE '8C967V' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(49:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(52:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(55:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(58:2)
           MOVE 'D0LBZK' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(61:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(64:2)
           MOVE 'GU3TTF' TO XF1-W
           REWRITE XF1-R FROM XF1-W
           END-REWRITE
           MOVE XF1-S TO TRC(67:2)
           READ XF1 INTO XF1-I
               AT END MOVE 'E' TO TRC(72:1)
           END-READ
           MOVE XF1-S TO TRC(70:2)
           MOVE XF1-R TO TRC(73:6)
           MOVE XF1-I TO TRC(79:6)
           READ XF1 NEXT RECORD INTO XF1-I
               AT END MOVE 'E' TO TRC(87:1)
               NOT AT END MOVE 'N' TO TRC(87:1)
           END-READ
           MOVE XF1-S TO TRC(85:2)
           MOVE XF1-R TO TRC(88:6)
           MOVE XF1-I TO TRC(94:6)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(100:2)
           MOVE 'NWDXIY' TO XF1-W
           REWRITE XF1-R FROM XF1-W
           END-REWRITE
           MOVE XF1-S TO TRC(103:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(106:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(109:2)
           READ XF1
               AT END MOVE 'E' TO TRC(114:1)
           END-READ
           MOVE XF1-S TO TRC(112:2)
           MOVE XF1-R TO TRC(115:6)
           READ XF1
               AT END MOVE 'E' TO TRC(123:1)
           END-READ
           MOVE XF1-S TO TRC(121:2)
           MOVE XF1-R TO TRC(124:6)
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
           READ XF1
               AT END MOVE 'E' TO TRC(204:1)
           END-READ
           MOVE XF1-S TO TRC(202:2)
           MOVE XF1-R TO TRC(205:6)
           READ XF1
               AT END MOVE 'E' TO TRC(213:1)
           END-READ
           MOVE XF1-S TO TRC(211:2)
           MOVE XF1-R TO TRC(214:6)
           READ XF1
               AT END MOVE 'E' TO TRC(222:1)
           END-READ
           MOVE XF1-S TO TRC(220:2)
           MOVE XF1-R TO TRC(223:6)
           READ XF1
               AT END MOVE 'E' TO TRC(231:1)
           END-READ
           MOVE XF1-S TO TRC(229:2)
           MOVE XF1-R TO TRC(232:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(238:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 262
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
