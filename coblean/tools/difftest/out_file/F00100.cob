       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00100.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00100_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00100_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF2-K
               FILE STATUS IS XF2-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-D PIC X(3).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(267) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 303.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           MOVE 'K037YS' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(6:1)
               NOT INVALID KEY MOVE 'N' TO TRC(6:1)
           END-WRITE
           MOVE XF2-S TO TRC(4:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(7:2)
           MOVE 'K08OJU' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(12:1)
               NOT INVALID KEY MOVE 'N' TO TRC(12:1)
           END-WRITE
           MOVE XF1-S TO TRC(10:2)
           MOVE 'K076NX' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(15:1)
           END-WRITE
           MOVE XF1-S TO TRC(13:2)
           MOVE 'K0741A' TO XF2-W
           WRITE XF2-R FROM XF2-W
               NOT INVALID KEY MOVE 'N' TO TRC(18:1)
           END-WRITE
           MOVE XF2-S TO TRC(16:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(19:2)
           MOVE 'K08HA4' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(24:1)
           END-WRITE
           MOVE XF1-S TO TRC(22:2)
           MOVE 'K02ZOR' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(27:1)
           END-WRITE
           MOVE XF1-S TO TRC(25:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(28:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(31:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(34:2)
           OPEN EXTEND XF2
           MOVE XF2-S TO TRC(37:2)
           READ XF1
               AT END MOVE 'E' TO TRC(42:1)
               NOT AT END MOVE 'N' TO TRC(42:1)
           END-READ
           MOVE XF1-S TO TRC(40:2)
           MOVE XF1-R TO TRC(43:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(49:2)
           MOVE 'K07' TO XF2-K
           READ XF2 KEY IS XF2-K
               INVALID KEY MOVE 'E' TO TRC(54:1)
           END-READ
           MOVE XF2-S TO TRC(52:2)
           MOVE XF2-R TO TRC(55:6)
           READ XF1
               AT END MOVE 'E' TO TRC(63:1)
               NOT AT END MOVE 'N' TO TRC(63:1)
           END-READ
           MOVE XF1-S TO TRC(61:2)
           MOVE XF1-R TO TRC(64:6)
           READ XF1
               AT END MOVE 'E' TO TRC(72:1)
               NOT AT END MOVE 'N' TO TRC(72:1)
           END-READ
           MOVE XF1-S TO TRC(70:2)
           MOVE XF1-R TO TRC(73:6)
           MOVE 'K03G9G' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(81:1)
               NOT INVALID KEY MOVE 'N' TO TRC(81:1)
           END-WRITE
           MOVE XF2-S TO TRC(79:2)
           MOVE 'K08ILH' TO XF1-W
           REWRITE XF1-R FROM XF1-W
           END-REWRITE
           MOVE XF1-S TO TRC(82:2)
           READ XF1 NEXT RECORD
               AT END MOVE 'E' TO TRC(87:1)
               NOT AT END MOVE 'N' TO TRC(87:1)
           END-READ
           MOVE XF1-S TO TRC(85:2)
           MOVE XF1-R TO TRC(88:6)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(94:2)
           MOVE 'K07MM7' TO XF2-R
           REWRITE XF2-R
           END-REWRITE
           MOVE XF2-S TO TRC(97:2)
           MOVE 'K07JZU' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(102:1)
           END-WRITE
           MOVE XF2-S TO TRC(100:2)
           READ XF1
               AT END MOVE 'E' TO TRC(105:1)
               NOT AT END MOVE 'N' TO TRC(105:1)
           END-READ
           MOVE XF1-S TO TRC(103:2)
           MOVE XF1-R TO TRC(106:6)
           MOVE 'K03PEN' TO XF2-W
           REWRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(114:1)
               NOT INVALID KEY MOVE 'N' TO TRC(114:1)
           END-REWRITE
           MOVE XF2-S TO TRC(112:2)
           MOVE 'K07HIS' TO XF2-R
           REWRITE XF2-R
           END-REWRITE
           MOVE XF2-S TO TRC(115:2)
           MOVE 'K05XJN' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(120:1)
           END-WRITE
           MOVE XF2-S TO TRC(118:2)
           READ XF1 INTO XF1-I
               AT END MOVE 'E' TO TRC(123:1)
               NOT AT END MOVE 'N' TO TRC(123:1)
           END-READ
           MOVE XF1-S TO TRC(121:2)
           MOVE XF1-R TO TRC(124:6)
           MOVE XF1-I TO TRC(130:6)
           READ XF1 NEXT RECORD INTO XF1-I
               AT END MOVE 'E' TO TRC(138:1)
           END-READ
           MOVE XF1-S TO TRC(136:2)
           MOVE XF1-R TO TRC(139:6)
           MOVE XF1-I TO TRC(145:6)
           READ XF1
               NOT AT END MOVE 'N' TO TRC(153:1)
           END-READ
           MOVE XF1-S TO TRC(151:2)
           MOVE XF1-R TO TRC(154:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(160:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(163:2)
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
           CLOSE XF1
           MOVE XF1-S TO TRC(184:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(187:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(190:2)
           MOVE 'K01' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(195:1)
           END-READ
           MOVE XF2-S TO TRC(193:2)
           MOVE XF2-R TO TRC(196:6)
           MOVE 'K02' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(204:1)
           END-READ
           MOVE XF2-S TO TRC(202:2)
           MOVE XF2-R TO TRC(205:6)
           MOVE 'K03' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(213:1)
           END-READ
           MOVE XF2-S TO TRC(211:2)
           MOVE XF2-R TO TRC(214:6)
           MOVE 'K04' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(222:1)
           END-READ
           MOVE XF2-S TO TRC(220:2)
           MOVE XF2-R TO TRC(223:6)
           MOVE 'K05' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(231:1)
           END-READ
           MOVE XF2-S TO TRC(229:2)
           MOVE XF2-R TO TRC(232:6)
           MOVE 'K06' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(240:1)
           END-READ
           MOVE XF2-S TO TRC(238:2)
           MOVE XF2-R TO TRC(241:6)
           MOVE 'K07' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(249:1)
           END-READ
           MOVE XF2-S TO TRC(247:2)
           MOVE XF2-R TO TRC(250:6)
           MOVE 'K08' TO XF2-K
           READ XF2
               INVALID KEY MOVE 'E' TO TRC(258:1)
           END-READ
           MOVE XF2-S TO TRC(256:2)
           MOVE XF2-R TO TRC(259:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(265:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 303
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
