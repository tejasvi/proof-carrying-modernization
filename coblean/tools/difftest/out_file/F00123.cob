       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00123.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00123_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00123_2.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00123_3.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF3-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-D PIC X(3).
       FD  XF2.
       01  XF2-R.
           05  XF2-D PIC X(6).
       FD  XF3.
       01  XF3-R.
           05  XF3-D PIC X(6).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(168) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(6) VALUE SPACES.
           05  XF3-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 218.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(1:2)
           MOVE 'WCHSTS' TO XF3-W
           REWRITE XF3-R FROM XF3-W
           END-REWRITE
           MOVE XF3-S TO TRC(4:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(7:2)
           MOVE 'K062QJ' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(12:1)
           END-WRITE
           MOVE XF1-S TO TRC(10:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(13:2)
           MOVE '8XTUCS' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(16:2)
           MOVE 'QYMBW3' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(19:2)
           MOVE 'K06NN7' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(22:2)
           MOVE 'B7C2PB' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(25:2)
           MOVE 'QCJMJ2' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(28:2)
           MOVE 'TLRMO6' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(31:2)
           MOVE '2NUE1G' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(34:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(37:2)
           MOVE '5MNNMF' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(40:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(43:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(46:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(49:2)
           READ XF1
               AT END MOVE 'E' TO TRC(54:1)
           END-READ
           MOVE XF1-S TO TRC(52:2)
           MOVE XF1-R TO TRC(55:6)
           READ XF1
               AT END MOVE 'E' TO TRC(63:1)
           END-READ
           MOVE XF1-S TO TRC(61:2)
           MOVE XF1-R TO TRC(64:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(70:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(73:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(76:2)
           READ XF2
               AT END MOVE 'E' TO TRC(81:1)
           END-READ
           MOVE XF2-S TO TRC(79:2)
           MOVE XF2-R TO TRC(82:6)
           READ XF2
               AT END MOVE 'E' TO TRC(90:1)
           END-READ
           MOVE XF2-S TO TRC(88:2)
           MOVE XF2-R TO TRC(91:6)
           READ XF2
               AT END MOVE 'E' TO TRC(99:1)
           END-READ
           MOVE XF2-S TO TRC(97:2)
           MOVE XF2-R TO TRC(100:6)
           READ XF2
               AT END MOVE 'E' TO TRC(108:1)
           END-READ
           MOVE XF2-S TO TRC(106:2)
           MOVE XF2-R TO TRC(109:6)
           READ XF2
               AT END MOVE 'E' TO TRC(117:1)
           END-READ
           MOVE XF2-S TO TRC(115:2)
           MOVE XF2-R TO TRC(118:6)
           READ XF2
               AT END MOVE 'E' TO TRC(126:1)
           END-READ
           MOVE XF2-S TO TRC(124:2)
           MOVE XF2-R TO TRC(127:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(133:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(136:2)
           READ XF3
               AT END MOVE 'E' TO TRC(141:1)
           END-READ
           MOVE XF3-S TO TRC(139:2)
           MOVE XF3-R TO TRC(142:6)
           READ XF3
               AT END MOVE 'E' TO TRC(150:1)
           END-READ
           MOVE XF3-S TO TRC(148:2)
           MOVE XF3-R TO TRC(151:6)
           READ XF3
               AT END MOVE 'E' TO TRC(159:1)
           END-READ
           MOVE XF3-S TO TRC(157:2)
           MOVE XF3-R TO TRC(160:6)
           CLOSE XF3
           MOVE XF3-S TO TRC(166:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 218
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
