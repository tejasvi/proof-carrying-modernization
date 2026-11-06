       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00087.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00087_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00087_2.dat'
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
           05  TRC PIC X(128) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 168.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           READ XF2
               AT END MOVE 'E' TO TRC(6:1)
               NOT AT END MOVE 'N' TO TRC(6:1)
           END-READ
           MOVE XF2-S TO TRC(4:2)
           MOVE XF2-R TO TRC(7:8)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(15:2)
           MOVE 'K012YU' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(18:2)
           MOVE 'K07UQW' TO XF1-W
           REWRITE XF1-R FROM XF1-W
           END-REWRITE
           MOVE XF1-S TO TRC(21:2)
           MOVE 'K0577X' TO XF1-W
           WRITE XF1-R FROM XF1-W
               NOT INVALID KEY MOVE 'N' TO TRC(26:1)
           END-WRITE
           MOVE XF1-S TO TRC(24:2)
           MOVE 'K08XHI' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(29:1)
               NOT INVALID KEY MOVE 'N' TO TRC(29:1)
           END-WRITE
           MOVE XF1-S TO TRC(27:2)
           MOVE 'K084EB' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(32:1)
           END-WRITE
           MOVE XF1-S TO TRC(30:2)
           READ XF2
               AT END MOVE 'E' TO TRC(35:1)
           END-READ
           MOVE XF2-S TO TRC(33:2)
           MOVE XF2-R TO TRC(36:8)
           MOVE 'K05A6BK8' TO XF2-R
           REWRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(46:1)
               NOT INVALID KEY MOVE 'N' TO TRC(46:1)
           END-REWRITE
           MOVE XF2-S TO TRC(44:2)
           MOVE 'K043VO' TO XF1-W
           WRITE XF1-R FROM XF1-W
               NOT INVALID KEY MOVE 'N' TO TRC(49:1)
           END-WRITE
           MOVE XF1-S TO TRC(47:2)
           MOVE 'K07A1A9Q' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(52:1)
           END-WRITE
           MOVE XF2-S TO TRC(50:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(53:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(56:2)
           READ XF1
               AT END MOVE 'E' TO TRC(61:1)
           END-READ
           MOVE XF1-S TO TRC(59:2)
           MOVE XF1-R TO TRC(62:6)
           READ XF1
               AT END MOVE 'E' TO TRC(70:1)
           END-READ
           MOVE XF1-S TO TRC(68:2)
           MOVE XF1-R TO TRC(71:6)
           READ XF1
               AT END MOVE 'E' TO TRC(79:1)
           END-READ
           MOVE XF1-S TO TRC(77:2)
           MOVE XF1-R TO TRC(80:6)
           READ XF1
               AT END MOVE 'E' TO TRC(88:1)
           END-READ
           MOVE XF1-S TO TRC(86:2)
           MOVE XF1-R TO TRC(89:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(95:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(98:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(101:2)
           READ XF2
               AT END MOVE 'E' TO TRC(106:1)
           END-READ
           MOVE XF2-S TO TRC(104:2)
           MOVE XF2-R TO TRC(107:8)
           READ XF2
               AT END MOVE 'E' TO TRC(117:1)
           END-READ
           MOVE XF2-S TO TRC(115:2)
           MOVE XF2-R TO TRC(118:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(126:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 168
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
