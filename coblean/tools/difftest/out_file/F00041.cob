       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00041.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00041_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00041_2.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00041_3.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF3-K
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
           05  XF3-K PIC X(3).
           05  XF3-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(249) VALUE SPACES.
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
           05  BYTE PIC X OCCURS 299.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(4:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(7:2)
           MOVE 'FJE7XY' TO XF2-W
           REWRITE XF2-R FROM XF2-W
           END-REWRITE
           MOVE XF2-S TO TRC(10:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(13:2)
           READ XF1 INTO XF1-I
               AT END MOVE 'E' TO TRC(18:1)
           END-READ
           MOVE XF1-S TO TRC(16:2)
           MOVE XF1-R TO TRC(19:6)
           MOVE XF1-I TO TRC(25:6)
           CLOSE XF3
           MOVE XF3-S TO TRC(31:2)
           OPEN I-O XF3
           MOVE XF3-S TO TRC(34:2)
           MOVE 'K08CZZ' TO XF3-R
           REWRITE XF3-R
           END-REWRITE
           MOVE XF3-S TO TRC(37:2)
           MOVE 'K03' TO XF3-K
           DELETE XF3 RECORD
               INVALID KEY MOVE 'E' TO TRC(42:1)
               NOT INVALID KEY MOVE 'N' TO TRC(42:1)
           END-DELETE
           MOVE XF3-S TO TRC(40:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(43:2)
           MOVE 'K04C64' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(48:1)
               NOT INVALID KEY MOVE 'N' TO TRC(48:1)
           END-WRITE
           MOVE XF1-S TO TRC(46:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(49:2)
           READ XF1
           END-READ
           MOVE XF1-S TO TRC(52:2)
           MOVE XF1-R TO TRC(55:6)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(61:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(64:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(67:2)
           MOVE 'C7OJY8' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE XF2-S TO TRC(70:2)
           READ XF2
               AT END MOVE 'E' TO TRC(75:1)
           END-READ
           MOVE XF2-S TO TRC(73:2)
           MOVE XF2-R TO TRC(76:6)
           READ XF2 NEXT RECORD
               AT END MOVE 'E' TO TRC(84:1)
               NOT AT END MOVE 'N' TO TRC(84:1)
           END-READ
           MOVE XF2-S TO TRC(82:2)
           MOVE XF2-R TO TRC(85:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(91:2)
           READ XF2
               AT END MOVE 'E' TO TRC(96:1)
               NOT AT END MOVE 'N' TO TRC(96:1)
           END-READ
           MOVE XF2-S TO TRC(94:2)
           MOVE XF2-R TO TRC(97:6)
           MOVE 'K048CB' TO XF3-R
           REWRITE XF3-R
           END-REWRITE
           MOVE XF3-S TO TRC(103:2)
           MOVE '7N5TOK' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(106:2)
           READ XF2 INTO XF2-I
               NOT AT END MOVE 'N' TO TRC(111:1)
           END-READ
           MOVE XF2-S TO TRC(109:2)
           MOVE XF2-R TO TRC(112:6)
           MOVE XF2-I TO TRC(118:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(124:2)
           READ XF1
               NOT AT END MOVE 'N' TO TRC(129:1)
           END-READ
           MOVE XF1-S TO TRC(127:2)
           MOVE XF1-R TO TRC(130:6)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(136:2)
           READ XF1
               AT END MOVE 'E' TO TRC(141:1)
           END-READ
           MOVE XF1-S TO TRC(139:2)
           MOVE XF1-R TO TRC(142:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(148:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(151:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(154:2)
           READ XF2
               AT END MOVE 'E' TO TRC(159:1)
           END-READ
           MOVE XF2-S TO TRC(157:2)
           MOVE XF2-R TO TRC(160:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(166:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(169:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(172:2)
           MOVE 'K01' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(177:1)
           END-READ
           MOVE XF3-S TO TRC(175:2)
           MOVE XF3-R TO TRC(178:6)
           MOVE 'K02' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(186:1)
           END-READ
           MOVE XF3-S TO TRC(184:2)
           MOVE XF3-R TO TRC(187:6)
           MOVE 'K03' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(195:1)
           END-READ
           MOVE XF3-S TO TRC(193:2)
           MOVE XF3-R TO TRC(196:6)
           MOVE 'K04' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(204:1)
           END-READ
           MOVE XF3-S TO TRC(202:2)
           MOVE XF3-R TO TRC(205:6)
           MOVE 'K05' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(213:1)
           END-READ
           MOVE XF3-S TO TRC(211:2)
           MOVE XF3-R TO TRC(214:6)
           MOVE 'K06' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(222:1)
           END-READ
           MOVE XF3-S TO TRC(220:2)
           MOVE XF3-R TO TRC(223:6)
           MOVE 'K07' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(231:1)
           END-READ
           MOVE XF3-S TO TRC(229:2)
           MOVE XF3-R TO TRC(232:6)
           MOVE 'K08' TO XF3-K
           READ XF3
               INVALID KEY MOVE 'E' TO TRC(240:1)
           END-READ
           MOVE XF3-S TO TRC(238:2)
           MOVE XF3-R TO TRC(241:6)
           CLOSE XF3
           MOVE XF3-S TO TRC(247:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 299
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
