       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00122.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00122_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00122_2.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF2-S.
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
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(156) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 196.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           MOVE 'K04A3XY4' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K04A638R' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(9:1)
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           MOVE 'K07A2BV5' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(12:1)
               NOT INVALID KEY MOVE 'N' TO TRC(12:1)
           END-WRITE
           MOVE XF1-S TO TRC(10:2)
           MOVE 'K08A2RBA' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(15:1)
           END-WRITE
           MOVE XF1-S TO TRC(13:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(16:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(19:2)
           READ XF1
           END-READ
           MOVE XF1-S TO TRC(22:2)
           MOVE XF1-R TO TRC(25:8)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(33:2)
           READ XF1
               AT END MOVE 'E' TO TRC(38:1)
               NOT AT END MOVE 'N' TO TRC(38:1)
           END-READ
           MOVE XF1-S TO TRC(36:2)
           MOVE XF1-R TO TRC(39:8)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(47:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(50:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(53:2)
           MOVE 'WN7FXX' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(56:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(59:2)
           MOVE 'K01A3832' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(62:2)
           MOVE 'K08A460J' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(67:1)
           END-WRITE
           MOVE XF1-S TO TRC(65:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(68:2)
           MOVE 'Q47Q0H' TO XF2-W
           REWRITE XF2-R FROM XF2-W
           END-REWRITE
           MOVE XF2-S TO TRC(71:2)
           MOVE 'K08A3GC8' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(74:2)
           MOVE 'K06A3WAD' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(77:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(80:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(83:2)
           READ XF1
               AT END MOVE 'E' TO TRC(88:1)
           END-READ
           MOVE XF1-S TO TRC(86:2)
           MOVE XF1-R TO TRC(89:8)
           READ XF1
               AT END MOVE 'E' TO TRC(99:1)
           END-READ
           MOVE XF1-S TO TRC(97:2)
           MOVE XF1-R TO TRC(100:8)
           READ XF1
               AT END MOVE 'E' TO TRC(110:1)
           END-READ
           MOVE XF1-S TO TRC(108:2)
           MOVE XF1-R TO TRC(111:8)
           READ XF1
               AT END MOVE 'E' TO TRC(121:1)
           END-READ
           MOVE XF1-S TO TRC(119:2)
           MOVE XF1-R TO TRC(122:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(130:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(133:2)
           READ XF2
               AT END MOVE 'E' TO TRC(138:1)
           END-READ
           MOVE XF2-S TO TRC(136:2)
           MOVE XF2-R TO TRC(139:6)
           READ XF2
               AT END MOVE 'E' TO TRC(147:1)
           END-READ
           MOVE XF2-S TO TRC(145:2)
           MOVE XF2-R TO TRC(148:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(154:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 196
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
