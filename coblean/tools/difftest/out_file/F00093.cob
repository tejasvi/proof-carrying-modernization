       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00093.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00093_1.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00093_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF2-K
               FILE STATUS IS XF2-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-D PIC X(6).
       FD  XF2.
       01  XF2-R.
           05  XF2-K PIC X(3).
           05  XF2-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(144) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 180.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K02LZG' TO XF2-R
           WRITE XF2-R
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF2-S TO TRC(7:2)
           MOVE 'K082EZ' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(12:1)
           END-WRITE
           MOVE XF2-S TO TRC(10:2)
           MOVE 'K060LZ' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(15:1)
           END-WRITE
           MOVE XF2-S TO TRC(13:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(16:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(19:2)
           MOVE 'C1PGZJ' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(22:2)
           MOVE 'FHNOA7' TO XF1-W
           REWRITE XF1-R FROM XF1-W
           END-REWRITE
           MOVE XF1-S TO TRC(25:2)
           MOVE '8SVCX8' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(28:2)
           MOVE 'K08L3H' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(31:2)
           READ XF1
               NOT AT END MOVE 'N' TO TRC(36:1)
           END-READ
           MOVE XF1-S TO TRC(34:2)
           MOVE XF1-R TO TRC(37:6)
           MOVE 'K06X49' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(45:1)
               NOT INVALID KEY MOVE 'N' TO TRC(45:1)
           END-WRITE
           MOVE XF2-S TO TRC(43:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(46:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(49:2)
           MOVE 'K07WL7' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(54:1)
               NOT INVALID KEY MOVE 'N' TO TRC(54:1)
           END-WRITE
           MOVE XF2-S TO TRC(52:2)
           MOVE 'K02VET' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(57:1)
               NOT INVALID KEY MOVE 'N' TO TRC(57:1)
           END-WRITE
           MOVE XF2-S TO TRC(55:2)
           MOVE 'K02GKZ' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(60:1)
               NOT INVALID KEY MOVE 'N' TO TRC(60:1)
           END-WRITE
           MOVE XF2-S TO TRC(58:2)
           MOVE '8LL1MX' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(61:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(64:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(67:2)
           READ XF1
           END-READ
           MOVE XF1-S TO TRC(70:2)
           MOVE XF1-R TO TRC(73:6)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(79:2)
           MOVE 'GVN7CC' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(82:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(85:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(88:2)
           READ XF1
               AT END MOVE 'E' TO TRC(93:1)
           END-READ
           MOVE XF1-S TO TRC(91:2)
           MOVE XF1-R TO TRC(94:6)
           READ XF1
               AT END MOVE 'E' TO TRC(102:1)
           END-READ
           MOVE XF1-S TO TRC(100:2)
           MOVE XF1-R TO TRC(103:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(109:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(112:2)
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
           READ XF2
               AT END MOVE 'E' TO TRC(135:1)
           END-READ
           MOVE XF2-S TO TRC(133:2)
           MOVE XF2-R TO TRC(136:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(142:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 180
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
