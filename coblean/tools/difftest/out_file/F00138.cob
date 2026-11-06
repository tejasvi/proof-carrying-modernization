       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00138.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00138_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00138_2.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL.
           SELECT XF3 ASSIGN TO 'F00138_3.dat'
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
           05  TRC PIC X(192) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(6) VALUE SPACES.
           05  XF3-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 240.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           CLOSE XF1
           MOVE XF1-S TO TRC(1:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(4:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(7:2)
           OPEN OUTPUT XF2
           MOVE '--' TO TRC(10:2)
           MOVE 'K07DE3' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(15:1)
           END-WRITE
           MOVE XF1-S TO TRC(13:2)
           MOVE 'Y82L0N' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(16:2)
           MOVE 'HU4KB2' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE '--' TO TRC(19:2)
           MOVE '6ET98A' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(22:2)
           CLOSE XF2
           MOVE '--' TO TRC(25:2)
           MOVE 'K07LI6' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(28:2)
           MOVE '3T705O' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(31:2)
           MOVE 'WX71Z7' TO XF3-W
           WRITE XF3-R FROM XF3-W
           END-WRITE
           MOVE XF3-S TO TRC(34:2)
           READ XF3
           END-READ
           MOVE XF3-S TO TRC(37:2)
           MOVE XF3-R TO TRC(40:6)
           MOVE 'G0WLMS' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(46:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(49:2)
           OPEN I-O XF3
           MOVE XF3-S TO TRC(52:2)
           MOVE 'K07NR8' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(57:1)
               NOT INVALID KEY MOVE 'N' TO TRC(57:1)
           END-WRITE
           MOVE XF1-S TO TRC(55:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(58:2)
           MOVE 'K0862L' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(61:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(64:2)
           OPEN I-O XF3
           MOVE XF3-S TO TRC(67:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(70:2)
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
           OPEN INPUT XF2
           MOVE '--' TO TRC(106:2)
           READ XF2
               AT END MOVE 'E' TO TRC(111:1)
           END-READ
           MOVE '--' TO TRC(109:2)
           MOVE XF2-R TO TRC(112:6)
           READ XF2
               AT END MOVE 'E' TO TRC(120:1)
           END-READ
           MOVE '--' TO TRC(118:2)
           MOVE XF2-R TO TRC(121:6)
           CLOSE XF2
           MOVE '--' TO TRC(127:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(130:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(133:2)
           READ XF3
               AT END MOVE 'E' TO TRC(138:1)
           END-READ
           MOVE XF3-S TO TRC(136:2)
           MOVE XF3-R TO TRC(139:6)
           READ XF3
               AT END MOVE 'E' TO TRC(147:1)
           END-READ
           MOVE XF3-S TO TRC(145:2)
           MOVE XF3-R TO TRC(148:6)
           READ XF3
               AT END MOVE 'E' TO TRC(156:1)
           END-READ
           MOVE XF3-S TO TRC(154:2)
           MOVE XF3-R TO TRC(157:6)
           READ XF3
               AT END MOVE 'E' TO TRC(165:1)
           END-READ
           MOVE XF3-S TO TRC(163:2)
           MOVE XF3-R TO TRC(166:6)
           READ XF3
               AT END MOVE 'E' TO TRC(174:1)
           END-READ
           MOVE XF3-S TO TRC(172:2)
           MOVE XF3-R TO TRC(175:6)
           READ XF3
               AT END MOVE 'E' TO TRC(183:1)
           END-READ
           MOVE XF3-S TO TRC(181:2)
           MOVE XF3-R TO TRC(184:6)
           CLOSE XF3
           MOVE XF3-S TO TRC(190:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 240
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
