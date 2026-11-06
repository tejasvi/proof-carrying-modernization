       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00074.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00074_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00074_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF2-K
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00074_3.dat'
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
           05  XF2-K PIC X(3).
           05  XF2-D PIC X(3).
       FD  XF3.
       01  XF3-R.
           05  XF3-D PIC X(6).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(204) VALUE SPACES.
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
           05  BYTE PIC X OCCURS 254.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(1:2)
           MOVE 'K02XNS' TO XF2-R
           REWRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(6:1)
           END-REWRITE
           MOVE XF2-S TO TRC(4:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(7:2)
           MOVE 'A4QTS1' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(10:2)
           MOVE 'K06AUG' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(13:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(16:2)
           MOVE 'K04782' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(21:1)
               NOT INVALID KEY MOVE 'N' TO TRC(21:1)
           END-WRITE
           MOVE XF2-S TO TRC(19:2)
           MOVE 'YD3YA7' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(22:2)
           READ XF1
           END-READ
           MOVE XF1-S TO TRC(25:2)
           MOVE XF1-R TO TRC(28:6)
           MOVE 'K052IC' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(36:1)
               NOT INVALID KEY MOVE 'N' TO TRC(36:1)
           END-WRITE
           MOVE XF2-S TO TRC(34:2)
           MOVE 'K07ZTA' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(39:1)
               NOT INVALID KEY MOVE 'N' TO TRC(39:1)
           END-WRITE
           MOVE XF1-S TO TRC(37:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(40:2)
           MOVE 'M42A5I' TO XF3-W
           WRITE XF3-R FROM XF3-W
           END-WRITE
           MOVE XF3-S TO TRC(43:2)
           MOVE 'K07WI8' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(46:2)
           MOVE 'K08PFT' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(51:1)
               NOT INVALID KEY MOVE 'N' TO TRC(51:1)
           END-WRITE
           MOVE XF1-S TO TRC(49:2)
           MOVE 'K03ZKN' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(54:1)
               NOT INVALID KEY MOVE 'N' TO TRC(54:1)
           END-WRITE
           MOVE XF1-S TO TRC(52:2)
           MOVE '6PMJYS' TO XF3-W
           REWRITE XF3-R FROM XF3-W
           END-REWRITE
           MOVE XF3-S TO TRC(55:2)
           OPEN EXTEND XF2
           MOVE XF2-S TO TRC(58:2)
           MOVE 'K044F4' TO XF2-R
           REWRITE XF2-R
           END-REWRITE
           MOVE XF2-S TO TRC(61:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(64:2)
           MOVE 'K06I0F' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE XF2-S TO TRC(67:2)
           MOVE 'VWIVQS' TO XF3-W
           WRITE XF3-R FROM XF3-W
           END-WRITE
           MOVE XF3-S TO TRC(70:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(73:2)
           READ XF1
               AT END MOVE 'E' TO TRC(78:1)
           END-READ
           MOVE XF1-S TO TRC(76:2)
           MOVE XF1-R TO TRC(79:6)
           READ XF1
               AT END MOVE 'E' TO TRC(87:1)
           END-READ
           MOVE XF1-S TO TRC(85:2)
           MOVE XF1-R TO TRC(88:6)
           READ XF1
               AT END MOVE 'E' TO TRC(96:1)
           END-READ
           MOVE XF1-S TO TRC(94:2)
           MOVE XF1-R TO TRC(97:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(103:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(106:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(109:2)
           READ XF2
               AT END MOVE 'E' TO TRC(114:1)
           END-READ
           MOVE XF2-S TO TRC(112:2)
           MOVE XF2-R TO TRC(115:6)
           READ XF2
               AT END MOVE 'E' TO TRC(123:1)
           END-READ
           MOVE XF2-S TO TRC(121:2)
           MOVE XF2-R TO TRC(124:6)
           READ XF2
               AT END MOVE 'E' TO TRC(132:1)
           END-READ
           MOVE XF2-S TO TRC(130:2)
           MOVE XF2-R TO TRC(133:6)
           READ XF2
               AT END MOVE 'E' TO TRC(141:1)
           END-READ
           MOVE XF2-S TO TRC(139:2)
           MOVE XF2-R TO TRC(142:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(148:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(151:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(154:2)
           READ XF3
               AT END MOVE 'E' TO TRC(159:1)
           END-READ
           MOVE XF3-S TO TRC(157:2)
           MOVE XF3-R TO TRC(160:6)
           READ XF3
               AT END MOVE 'E' TO TRC(168:1)
           END-READ
           MOVE XF3-S TO TRC(166:2)
           MOVE XF3-R TO TRC(169:6)
           READ XF3
               AT END MOVE 'E' TO TRC(177:1)
           END-READ
           MOVE XF3-S TO TRC(175:2)
           MOVE XF3-R TO TRC(178:6)
           READ XF3
               AT END MOVE 'E' TO TRC(186:1)
           END-READ
           MOVE XF3-S TO TRC(184:2)
           MOVE XF3-R TO TRC(187:6)
           READ XF3
               AT END MOVE 'E' TO TRC(195:1)
           END-READ
           MOVE XF3-S TO TRC(193:2)
           MOVE XF3-R TO TRC(196:6)
           CLOSE XF3
           MOVE XF3-S TO TRC(202:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 254
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
