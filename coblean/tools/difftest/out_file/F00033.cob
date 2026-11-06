       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00033.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00033_1.dat'
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
           05  TRC PIC X(165) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 187.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           MOVE 'K07M01' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(6:1)
               NOT INVALID KEY MOVE 'N' TO TRC(6:1)
           END-WRITE
           MOVE XF1-S TO TRC(4:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(7:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(10:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(13:2)
           READ XF1 NEXT RECORD INTO XF1-I
               NOT AT END MOVE 'N' TO TRC(18:1)
           END-READ
           MOVE XF1-S TO TRC(16:2)
           MOVE XF1-R TO TRC(19:6)
           MOVE XF1-I TO TRC(25:6)
           MOVE 'K078SY' TO XF1-W
           REWRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(33:1)
               NOT INVALID KEY MOVE 'N' TO TRC(33:1)
           END-REWRITE
           MOVE XF1-S TO TRC(31:2)
           MOVE 'K05UHG' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(36:1)
               NOT INVALID KEY MOVE 'N' TO TRC(36:1)
           END-WRITE
           MOVE XF1-S TO TRC(34:2)
           READ XF1 INTO XF1-I
           END-READ
           MOVE XF1-S TO TRC(37:2)
           MOVE XF1-R TO TRC(40:6)
           MOVE XF1-I TO TRC(46:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(52:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(55:2)
           MOVE 'K03M3R' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(60:1)
               NOT INVALID KEY MOVE 'N' TO TRC(60:1)
           END-WRITE
           MOVE XF1-S TO TRC(58:2)
           MOVE 'K08DQP' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(63:1)
           END-WRITE
           MOVE XF1-S TO TRC(61:2)
           MOVE 'K04BN5' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(66:1)
           END-WRITE
           MOVE XF1-S TO TRC(64:2)
           MOVE 'K03FN3' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(69:1)
           END-WRITE
           MOVE XF1-S TO TRC(67:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(70:2)
           MOVE 'K01ZMW' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(75:1)
           END-WRITE
           MOVE XF1-S TO TRC(73:2)
           MOVE 'K03ELP' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(76:2)
           READ XF1 NEXT RECORD
               AT END MOVE 'E' TO TRC(81:1)
               NOT AT END MOVE 'N' TO TRC(81:1)
           END-READ
           MOVE XF1-S TO TRC(79:2)
           MOVE XF1-R TO TRC(82:6)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(88:2)
           MOVE 'K078EP' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(91:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(94:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(97:2)
           MOVE 'K02WXJ' TO XF1-W
           REWRITE XF1-R FROM XF1-W
               NOT INVALID KEY MOVE 'N' TO TRC(102:1)
           END-REWRITE
           MOVE XF1-S TO TRC(100:2)
           MOVE 'K07IA2' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(105:1)
           END-WRITE
           MOVE XF1-S TO TRC(103:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(106:2)
           READ XF1
               AT END MOVE 'E' TO TRC(111:1)
               NOT AT END MOVE 'N' TO TRC(111:1)
           END-READ
           MOVE XF1-S TO TRC(109:2)
           MOVE XF1-R TO TRC(112:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(118:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(121:2)
           MOVE 'K07RX5' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(126:1)
           END-WRITE
           MOVE XF1-S TO TRC(124:2)
           MOVE 'K086B5' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(129:1)
               NOT INVALID KEY MOVE 'N' TO TRC(129:1)
           END-WRITE
           MOVE XF1-S TO TRC(127:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(130:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(133:2)
           READ XF1
               AT END MOVE 'E' TO TRC(138:1)
           END-READ
           MOVE XF1-S TO TRC(136:2)
           MOVE XF1-R TO TRC(139:6)
           READ XF1
               AT END MOVE 'E' TO TRC(147:1)
           END-READ
           MOVE XF1-S TO TRC(145:2)
           MOVE XF1-R TO TRC(148:6)
           READ XF1
               AT END MOVE 'E' TO TRC(156:1)
           END-READ
           MOVE XF1-S TO TRC(154:2)
           MOVE XF1-R TO TRC(157:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(163:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 187
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
