       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00095.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00095_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00095_2.dat'
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
           05  XF1-D PIC X(3).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-A PIC X(2).
           05  XF2-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(195) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 235.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K0786U' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(9:1)
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           MOVE 'K08M1O' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(12:1)
               NOT INVALID KEY MOVE 'N' TO TRC(12:1)
           END-WRITE
           MOVE XF1-S TO TRC(10:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(13:2)
           MOVE 'K01WPC' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(16:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(19:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(22:2)
           READ XF2
           END-READ
           MOVE XF2-S TO TRC(25:2)
           MOVE XF2-R TO TRC(28:8)
           MOVE 'K03S45' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(38:1)
           END-WRITE
           MOVE XF1-S TO TRC(36:2)
           MOVE 'K02YHR' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(41:1)
           END-WRITE
           MOVE XF1-S TO TRC(39:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(42:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(45:2)
           MOVE 'K06LIP' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(48:2)
           MOVE 'K07Z5F' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(53:1)
           END-WRITE
           MOVE XF1-S TO TRC(51:2)
           READ XF2
               AT END MOVE 'E' TO TRC(56:1)
               NOT AT END MOVE 'N' TO TRC(56:1)
           END-READ
           MOVE XF2-S TO TRC(54:2)
           MOVE XF2-R TO TRC(57:8)
           READ XF2 NEXT RECORD INTO XF2-I
               AT END MOVE 'E' TO TRC(67:1)
               NOT AT END MOVE 'N' TO TRC(67:1)
           END-READ
           MOVE XF2-S TO TRC(65:2)
           MOVE XF2-R TO TRC(68:8)
           MOVE XF2-I TO TRC(76:8)
           READ XF1 INTO XF1-I
           END-READ
           MOVE XF1-S TO TRC(84:2)
           MOVE XF1-R TO TRC(87:6)
           MOVE XF1-I TO TRC(93:6)
           MOVE 'K02YQY' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(101:1)
               NOT INVALID KEY MOVE 'N' TO TRC(101:1)
           END-WRITE
           MOVE XF1-S TO TRC(99:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(102:2)
           READ XF1 NEXT RECORD
               AT END MOVE 'E' TO TRC(107:1)
               NOT AT END MOVE 'N' TO TRC(107:1)
           END-READ
           MOVE XF1-S TO TRC(105:2)
           MOVE XF1-R TO TRC(108:6)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(114:2)
           READ XF1
               AT END MOVE 'E' TO TRC(119:1)
               NOT AT END MOVE 'N' TO TRC(119:1)
           END-READ
           MOVE XF1-S TO TRC(117:2)
           MOVE XF1-R TO TRC(120:6)
           READ XF2 NEXT RECORD
               AT END MOVE 'E' TO TRC(128:1)
           END-READ
           MOVE XF2-S TO TRC(126:2)
           MOVE XF2-R TO TRC(129:8)
           MOVE 'K06A6I0U' TO XF2-W
           REWRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(139:1)
               NOT INVALID KEY MOVE 'N' TO TRC(139:1)
           END-REWRITE
           MOVE XF2-S TO TRC(137:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(140:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(143:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(146:2)
           READ XF1
               AT END MOVE 'E' TO TRC(151:1)
           END-READ
           MOVE XF1-S TO TRC(149:2)
           MOVE XF1-R TO TRC(152:6)
           READ XF1
               AT END MOVE 'E' TO TRC(160:1)
           END-READ
           MOVE XF1-S TO TRC(158:2)
           MOVE XF1-R TO TRC(161:6)
           READ XF1
               AT END MOVE 'E' TO TRC(169:1)
           END-READ
           MOVE XF1-S TO TRC(167:2)
           MOVE XF1-R TO TRC(170:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(176:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(179:2)
           READ XF2
               AT END MOVE 'E' TO TRC(184:1)
           END-READ
           MOVE XF2-S TO TRC(182:2)
           MOVE XF2-R TO TRC(185:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(193:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 235
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
