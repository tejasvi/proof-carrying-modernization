       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00191.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00191_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               ALTERNATE RECORD KEY IS XF1-A
               FILE STATUS IS XF1-S.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-A PIC X(2).
           05  XF1-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(100) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 126.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(4:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(7:2)
           READ XF1
               NOT AT END MOVE 'N' TO TRC(12:1)
           END-READ
           MOVE XF1-S TO TRC(10:2)
           MOVE XF1-R TO TRC(13:8)
           MOVE 'K08A69LE' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(23:1)
           END-WRITE
           MOVE XF1-S TO TRC(21:2)
           MOVE 'K06A5N49' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(26:1)
           END-WRITE
           MOVE XF1-S TO TRC(24:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(27:2)
           MOVE 'K08A3SPG' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(32:1)
           END-WRITE
           MOVE XF1-S TO TRC(30:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(33:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(36:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(39:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(42:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(45:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(48:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(51:2)
           MOVE 'K02A34GV' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(56:1)
           END-WRITE
           MOVE XF1-S TO TRC(54:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(57:2)
           MOVE 'K06A3SJJ' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(60:2)
           MOVE 'K05A3LCP' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(65:1)
               NOT INVALID KEY MOVE 'N' TO TRC(65:1)
           END-WRITE
           MOVE XF1-S TO TRC(63:2)
           MOVE 'K01A6A0X' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(68:1)
           END-WRITE
           MOVE XF1-S TO TRC(66:2)
           MOVE 'K04A15G1' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(71:1)
           END-WRITE
           MOVE XF1-S TO TRC(69:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(72:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(75:2)
           MOVE 'K05A38GO' TO XF1-R
           REWRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(80:1)
               NOT INVALID KEY MOVE 'N' TO TRC(80:1)
           END-REWRITE
           MOVE XF1-S TO TRC(78:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(81:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(84:2)
           READ XF1
               AT END MOVE 'E' TO TRC(89:1)
           END-READ
           MOVE XF1-S TO TRC(87:2)
           MOVE XF1-R TO TRC(90:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(98:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 126
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
