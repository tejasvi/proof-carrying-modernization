       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00159.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00159_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
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
           05  TRC PIC X(180) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 202.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           MOVE 'K04W91' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(6:1)
               NOT INVALID KEY MOVE 'N' TO TRC(6:1)
           END-WRITE
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K081MN' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(9:1)
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(10:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(13:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(16:2)
           MOVE 'K045QJ' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(21:1)
           END-WRITE
           MOVE XF1-S TO TRC(19:2)
           MOVE 'K020T5' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(24:1)
               NOT INVALID KEY MOVE 'N' TO TRC(24:1)
           END-WRITE
           MOVE XF1-S TO TRC(22:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(25:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(28:2)
           MOVE 'K0675I' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(33:1)
           END-WRITE
           MOVE XF1-S TO TRC(31:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(34:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(37:2)
           MOVE 'K04AYL' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(42:1)
               NOT INVALID KEY MOVE 'N' TO TRC(42:1)
           END-WRITE
           MOVE XF1-S TO TRC(40:2)
           MOVE 'K063WJ' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(45:1)
               NOT INVALID KEY MOVE 'N' TO TRC(45:1)
           END-WRITE
           MOVE XF1-S TO TRC(43:2)
           MOVE 'K04EZG' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(46:2)
           MOVE 'K01FCW' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(51:1)
           END-WRITE
           MOVE XF1-S TO TRC(49:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(52:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(55:2)
           READ XF1
               AT END MOVE 'E' TO TRC(60:1)
               NOT AT END MOVE 'N' TO TRC(60:1)
           END-READ
           MOVE XF1-S TO TRC(58:2)
           MOVE XF1-R TO TRC(61:6)
           READ XF1
               NOT AT END MOVE 'N' TO TRC(69:1)
           END-READ
           MOVE XF1-S TO TRC(67:2)
           MOVE XF1-R TO TRC(70:6)
           READ XF1
               AT END MOVE 'E' TO TRC(78:1)
               NOT AT END MOVE 'N' TO TRC(78:1)
           END-READ
           MOVE XF1-S TO TRC(76:2)
           MOVE XF1-R TO TRC(79:6)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(85:2)
           READ XF1
               AT END MOVE 'E' TO TRC(90:1)
           END-READ
           MOVE XF1-S TO TRC(88:2)
           MOVE XF1-R TO TRC(91:6)
           READ XF1
           END-READ
           MOVE XF1-S TO TRC(97:2)
           MOVE XF1-R TO TRC(100:6)
           READ XF1
               AT END MOVE 'E' TO TRC(108:1)
               NOT AT END MOVE 'N' TO TRC(108:1)
           END-READ
           MOVE XF1-S TO TRC(106:2)
           MOVE XF1-R TO TRC(109:6)
           READ XF1 INTO XF1-I
               AT END MOVE 'E' TO TRC(117:1)
           END-READ
           MOVE XF1-S TO TRC(115:2)
           MOVE XF1-R TO TRC(118:6)
           MOVE XF1-I TO TRC(124:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(130:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(133:2)
           MOVE 'K031RK' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(138:1)
           END-WRITE
           MOVE XF1-S TO TRC(136:2)
           MOVE 'K05DG0' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(141:1)
               NOT INVALID KEY MOVE 'N' TO TRC(141:1)
           END-WRITE
           MOVE XF1-S TO TRC(139:2)
           MOVE 'K057GF' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(144:1)
           END-WRITE
           MOVE XF1-S TO TRC(142:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(145:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(148:2)
           READ XF1
               AT END MOVE 'E' TO TRC(153:1)
           END-READ
           MOVE XF1-S TO TRC(151:2)
           MOVE XF1-R TO TRC(154:6)
           READ XF1
               AT END MOVE 'E' TO TRC(162:1)
           END-READ
           MOVE XF1-S TO TRC(160:2)
           MOVE XF1-R TO TRC(163:6)
           READ XF1
               AT END MOVE 'E' TO TRC(171:1)
           END-READ
           MOVE XF1-S TO TRC(169:2)
           MOVE XF1-R TO TRC(172:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(178:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 202
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
