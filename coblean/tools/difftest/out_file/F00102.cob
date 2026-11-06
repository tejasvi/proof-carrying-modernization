       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00102.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00102_1.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL.
           SELECT XF2 ASSIGN TO 'F00102_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF2-K
               ALTERNATE RECORD KEY IS XF2-A
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00102_3.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF3-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-D PIC X(6).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-A PIC X(2).
           05  XF2-D PIC X(3).
       FD  XF3.
       01  XF3-R.
           05  XF3-D PIC X(6).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(174) VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(6) VALUE SPACES.
           05  XF3-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 226.
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
           OPEN OUTPUT XF1
           MOVE '--' TO TRC(7:2)
           MOVE 'K03A48X5' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(12:1)
               NOT INVALID KEY MOVE 'N' TO TRC(12:1)
           END-WRITE
           MOVE XF2-S TO TRC(10:2)
           MOVE '5UV37S' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(13:2)
           MOVE 'D0V8K2' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(16:2)
           MOVE 'K07A6ZF6' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(21:1)
           END-WRITE
           MOVE XF2-S TO TRC(19:2)
           MOVE '1TQ6C8' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE '--' TO TRC(22:2)
           MOVE '5RX1Z0' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE '--' TO TRC(25:2)
           MOVE 'K08A6N2K' TO XF2-R
           WRITE XF2-R
               NOT INVALID KEY MOVE 'N' TO TRC(30:1)
           END-WRITE
           MOVE XF2-S TO TRC(28:2)
           MOVE 'UKN0QK' TO XF3-R
           REWRITE XF3-R
           END-REWRITE
           MOVE XF3-S TO TRC(31:2)
           MOVE 'U2PQDG' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE '--' TO TRC(34:2)
           MOVE 'TYBJIJ' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE '--' TO TRC(37:2)
           MOVE 'K07A151L' TO XF2-R
           WRITE XF2-R
               NOT INVALID KEY MOVE 'N' TO TRC(42:1)
           END-WRITE
           MOVE XF2-S TO TRC(40:2)
           CLOSE XF1
           MOVE '--' TO TRC(43:2)
           OPEN INPUT XF1
           MOVE '--' TO TRC(46:2)
           READ XF1
               AT END MOVE 'E' TO TRC(51:1)
           END-READ
           MOVE '--' TO TRC(49:2)
           MOVE XF1-R TO TRC(52:6)
           READ XF1
               AT END MOVE 'E' TO TRC(60:1)
           END-READ
           MOVE '--' TO TRC(58:2)
           MOVE XF1-R TO TRC(61:6)
           READ XF1
               AT END MOVE 'E' TO TRC(69:1)
           END-READ
           MOVE '--' TO TRC(67:2)
           MOVE XF1-R TO TRC(70:6)
           READ XF1
               AT END MOVE 'E' TO TRC(78:1)
           END-READ
           MOVE '--' TO TRC(76:2)
           MOVE XF1-R TO TRC(79:6)
           READ XF1
               AT END MOVE 'E' TO TRC(87:1)
           END-READ
           MOVE '--' TO TRC(85:2)
           MOVE XF1-R TO TRC(88:6)
           CLOSE XF1
           MOVE '--' TO TRC(94:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(97:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(100:2)
           READ XF2
               AT END MOVE 'E' TO TRC(105:1)
           END-READ
           MOVE XF2-S TO TRC(103:2)
           MOVE XF2-R TO TRC(106:8)
           READ XF2
               AT END MOVE 'E' TO TRC(116:1)
           END-READ
           MOVE XF2-S TO TRC(114:2)
           MOVE XF2-R TO TRC(117:8)
           READ XF2
               AT END MOVE 'E' TO TRC(127:1)
           END-READ
           MOVE XF2-S TO TRC(125:2)
           MOVE XF2-R TO TRC(128:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(136:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(139:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(142:2)
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
           CLOSE XF3
           MOVE XF3-S TO TRC(172:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 226
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
