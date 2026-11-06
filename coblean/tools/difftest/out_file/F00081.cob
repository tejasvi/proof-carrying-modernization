       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00081.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00081_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00081_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF2-K
               ALTERNATE RECORD KEY IS XF2-A
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00081_3.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-A PIC X(2).
           05  XF1-D PIC X(3).
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
           05  TRC PIC X(122) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
           05  XF3-I PIC X(6) VALUE SPACES.
           05  XF3-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 178.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           OPEN EXTEND XF2
           MOVE XF2-S TO TRC(4:2)
           MOVE 'K06A62Z4' TO XF2-W
           WRITE XF2-R FROM XF2-W
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF2-S TO TRC(7:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(10:2)
           MOVE 'K08A243F' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(15:1)
               NOT INVALID KEY MOVE 'N' TO TRC(15:1)
           END-WRITE
           MOVE XF1-S TO TRC(13:2)
           MOVE 'K02A2NKK' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(18:1)
           END-WRITE
           MOVE XF1-S TO TRC(16:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(19:2)
           MOVE 'K03A2YPI' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(24:1)
               NOT INVALID KEY MOVE 'N' TO TRC(24:1)
           END-WRITE
           MOVE XF1-S TO TRC(22:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(25:2)
           MOVE 'K07A6K97' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(28:2)
           OPEN OUTPUT XF3
           MOVE '--' TO TRC(31:2)
           MOVE 'K08A6CXE' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(34:2)
           MOVE 'K02A5T3H' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(39:1)
               NOT INVALID KEY MOVE 'N' TO TRC(39:1)
           END-WRITE
           MOVE XF1-S TO TRC(37:2)
           MOVE 'K04A6C8R' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(42:1)
           END-WRITE
           MOVE XF1-S TO TRC(40:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(43:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(46:2)
           READ XF1
               AT END MOVE 'E' TO TRC(51:1)
           END-READ
           MOVE XF1-S TO TRC(49:2)
           MOVE XF1-R TO TRC(52:8)
           READ XF1
               AT END MOVE 'E' TO TRC(62:1)
           END-READ
           MOVE XF1-S TO TRC(60:2)
           MOVE XF1-R TO TRC(63:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(71:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(74:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(77:2)
           READ XF2
               AT END MOVE 'E' TO TRC(82:1)
           END-READ
           MOVE XF2-S TO TRC(80:2)
           MOVE XF2-R TO TRC(83:8)
           READ XF2
               AT END MOVE 'E' TO TRC(93:1)
           END-READ
           MOVE XF2-S TO TRC(91:2)
           MOVE XF2-R TO TRC(94:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(102:2)
           CLOSE XF3
           MOVE '--' TO TRC(105:2)
           OPEN INPUT XF3
           MOVE '--' TO TRC(108:2)
           READ XF3
               AT END MOVE 'E' TO TRC(113:1)
           END-READ
           MOVE '--' TO TRC(111:2)
           MOVE XF3-R TO TRC(114:6)
           CLOSE XF3
           MOVE '--' TO TRC(120:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 178
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
