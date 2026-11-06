       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00090.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00090_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00090_2.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00090_3.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF3-K
               ALTERNATE RECORD KEY IS XF3-A
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
           05  XF3-K PIC X(3).
           05  XF3-A PIC X(2).
           05  XF3-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(132) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(8) VALUE SPACES.
           05  XF3-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 190.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(4:2)
           MOVE 'K07A1OHG' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(9:1)
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(10:2)
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(13:2)
           MOVE 'K07A16J4' TO XF3-R
           WRITE XF3-R
               INVALID KEY MOVE 'E' TO TRC(18:1)
               NOT INVALID KEY MOVE 'N' TO TRC(18:1)
           END-WRITE
           MOVE XF3-S TO TRC(16:2)
           MOVE 'K08A55ZV' TO XF3-R
           WRITE XF3-R
               INVALID KEY MOVE 'E' TO TRC(21:1)
               NOT INVALID KEY MOVE 'N' TO TRC(21:1)
           END-WRITE
           MOVE XF3-S TO TRC(19:2)
           OPEN EXTEND XF2
           MOVE XF2-S TO TRC(22:2)
           MOVE 'K08A6V9A' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(25:2)
           MOVE 'K08A3X8Q' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(30:1)
               NOT INVALID KEY MOVE 'N' TO TRC(30:1)
           END-WRITE
           MOVE XF1-S TO TRC(28:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(31:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(34:2)
           READ XF1
               AT END MOVE 'E' TO TRC(39:1)
           END-READ
           MOVE XF1-S TO TRC(37:2)
           MOVE XF1-R TO TRC(40:8)
           READ XF1
               AT END MOVE 'E' TO TRC(50:1)
           END-READ
           MOVE XF1-S TO TRC(48:2)
           MOVE XF1-R TO TRC(51:8)
           READ XF1
               AT END MOVE 'E' TO TRC(61:1)
           END-READ
           MOVE XF1-S TO TRC(59:2)
           MOVE XF1-R TO TRC(62:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(70:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(73:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(76:2)
           READ XF2
               AT END MOVE 'E' TO TRC(81:1)
           END-READ
           MOVE XF2-S TO TRC(79:2)
           MOVE XF2-R TO TRC(82:6)
           CLOSE XF2
           MOVE XF2-S TO TRC(88:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(91:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(94:2)
           READ XF3
               AT END MOVE 'E' TO TRC(99:1)
           END-READ
           MOVE XF3-S TO TRC(97:2)
           MOVE XF3-R TO TRC(100:8)
           READ XF3
               AT END MOVE 'E' TO TRC(110:1)
           END-READ
           MOVE XF3-S TO TRC(108:2)
           MOVE XF3-R TO TRC(111:8)
           READ XF3
               AT END MOVE 'E' TO TRC(121:1)
           END-READ
           MOVE XF3-S TO TRC(119:2)
           MOVE XF3-R TO TRC(122:8)
           CLOSE XF3
           MOVE XF3-S TO TRC(130:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 190
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
