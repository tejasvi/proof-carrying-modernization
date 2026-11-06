       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00156.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00156_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00156_2.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00156_3.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF3-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-A PIC X(2).
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
           05  TRC PIC X(227) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(6) VALUE SPACES.
           05  XF3-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 281.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(4:2)
           READ XF3
               AT END MOVE 'E' TO TRC(9:1)
           END-READ
           MOVE XF3-S TO TRC(7:2)
           MOVE XF3-R TO TRC(10:6)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(16:2)
           MOVE 'CIM7NW' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(19:2)
           MOVE 'ADAT14' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(22:2)
           READ XF2 NEXT RECORD
           END-READ
           MOVE XF2-S TO TRC(25:2)
           MOVE XF2-R TO TRC(28:6)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(34:2)
           MOVE 'K04A3TW6' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(37:2)
           MOVE 'K05A4HCR' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(42:1)
               NOT INVALID KEY MOVE 'N' TO TRC(42:1)
           END-WRITE
           MOVE XF1-S TO TRC(40:2)
           OPEN I-O XF3
           MOVE XF3-S TO TRC(43:2)
           MOVE '8AC69A' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE XF2-S TO TRC(46:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(49:2)
           MOVE 'K07A3H5B' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(52:2)
           MOVE 'KVYYDR' TO XF3-W
           WRITE XF3-R FROM XF3-W
           END-WRITE
           MOVE XF3-S TO TRC(55:2)
           MOVE 'H7YGVM' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(58:2)
           MOVE 'K06A41SC' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(63:1)
           END-WRITE
           MOVE XF1-S TO TRC(61:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(64:2)
           MOVE 'K05A3LTG' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(69:1)
           END-WRITE
           MOVE XF1-S TO TRC(67:2)
           MOVE 'K08A3NH0' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(72:1)
               NOT INVALID KEY MOVE 'N' TO TRC(72:1)
           END-WRITE
           MOVE XF1-S TO TRC(70:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(73:2)
           MOVE 'K06A5YMU' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(78:1)
           END-WRITE
           MOVE XF1-S TO TRC(76:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(79:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(82:2)
           READ XF3
               NOT AT END MOVE 'N' TO TRC(87:1)
           END-READ
           MOVE XF3-S TO TRC(85:2)
           MOVE XF3-R TO TRC(88:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(94:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(97:2)
           READ XF1
               AT END MOVE 'E' TO TRC(102:1)
           END-READ
           MOVE XF1-S TO TRC(100:2)
           MOVE XF1-R TO TRC(103:8)
           READ XF1
               AT END MOVE 'E' TO TRC(113:1)
           END-READ
           MOVE XF1-S TO TRC(111:2)
           MOVE XF1-R TO TRC(114:8)
           READ XF1
               AT END MOVE 'E' TO TRC(124:1)
           END-READ
           MOVE XF1-S TO TRC(122:2)
           MOVE XF1-R TO TRC(125:8)
           READ XF1
               AT END MOVE 'E' TO TRC(135:1)
           END-READ
           MOVE XF1-S TO TRC(133:2)
           MOVE XF1-R TO TRC(136:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(144:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(147:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(150:2)
           READ XF2
               AT END MOVE 'E' TO TRC(155:1)
           END-READ
           MOVE XF2-S TO TRC(153:2)
           MOVE XF2-R TO TRC(156:6)
           READ XF2
               AT END MOVE 'E' TO TRC(164:1)
           END-READ
           MOVE XF2-S TO TRC(162:2)
           MOVE XF2-R TO TRC(165:6)
           READ XF2
               AT END MOVE 'E' TO TRC(173:1)
           END-READ
           MOVE XF2-S TO TRC(171:2)
           MOVE XF2-R TO TRC(174:6)
           READ XF2
               AT END MOVE 'E' TO TRC(182:1)
           END-READ
           MOVE XF2-S TO TRC(180:2)
           MOVE XF2-R TO TRC(183:6)
           READ XF2
               AT END MOVE 'E' TO TRC(191:1)
           END-READ
           MOVE XF2-S TO TRC(189:2)
           MOVE XF2-R TO TRC(192:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(198:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(201:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(204:2)
           READ XF3
               AT END MOVE 'E' TO TRC(209:1)
           END-READ
           MOVE XF3-S TO TRC(207:2)
           MOVE XF3-R TO TRC(210:6)
           READ XF3
               AT END MOVE 'E' TO TRC(218:1)
           END-READ
           MOVE XF3-S TO TRC(216:2)
           MOVE XF3-R TO TRC(219:6)
           CLOSE XF3
           MOVE XF3-S TO TRC(225:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 281
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
