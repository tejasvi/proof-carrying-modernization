       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00148.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00148_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00148_2.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL.
       DATA DIVISION.
       FILE SECTION.
       FD  XF1.
       01  XF1-R.
           05  XF1-K PIC X(3).
           05  XF1-D PIC X(3).
       FD  XF2.
       01  XF2-R.
           05  XF2-D PIC X(6).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(144) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-I PIC X(6) VALUE SPACES.
           05  XF2-W PIC X(6) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 178.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF2
           MOVE '--' TO TRC(1:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K069RJ' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(10:2)
           MOVE 'JU4LIR' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE '--' TO TRC(13:2)
           MOVE 'NW9DU1' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE '--' TO TRC(16:2)
           MOVE 'OFHWXZ' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE '--' TO TRC(19:2)
           MOVE 'QVDL1M' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE '--' TO TRC(22:2)
           MOVE 'K084BV' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(27:1)
               NOT INVALID KEY MOVE 'N' TO TRC(27:1)
           END-WRITE
           MOVE XF1-S TO TRC(25:2)
           MOVE 'ZSX6OT' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE '--' TO TRC(28:2)
           MOVE 'K08BJ5' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(31:2)
           MOVE 'QOYO09' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE '--' TO TRC(34:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(37:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(40:2)
           READ XF1
               AT END MOVE 'E' TO TRC(45:1)
           END-READ
           MOVE XF1-S TO TRC(43:2)
           MOVE XF1-R TO TRC(46:6)
           READ XF1
               AT END MOVE 'E' TO TRC(54:1)
           END-READ
           MOVE XF1-S TO TRC(52:2)
           MOVE XF1-R TO TRC(55:6)
           READ XF1
               AT END MOVE 'E' TO TRC(63:1)
           END-READ
           MOVE XF1-S TO TRC(61:2)
           MOVE XF1-R TO TRC(64:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(70:2)
           CLOSE XF2
           MOVE '--' TO TRC(73:2)
           OPEN INPUT XF2
           MOVE '--' TO TRC(76:2)
           READ XF2
               AT END MOVE 'E' TO TRC(81:1)
           END-READ
           MOVE '--' TO TRC(79:2)
           MOVE XF2-R TO TRC(82:6)
           READ XF2
               AT END MOVE 'E' TO TRC(90:1)
           END-READ
           MOVE '--' TO TRC(88:2)
           MOVE XF2-R TO TRC(91:6)
           READ XF2
               AT END MOVE 'E' TO TRC(99:1)
           END-READ
           MOVE '--' TO TRC(97:2)
           MOVE XF2-R TO TRC(100:6)
           READ XF2
               AT END MOVE 'E' TO TRC(108:1)
           END-READ
           MOVE '--' TO TRC(106:2)
           MOVE XF2-R TO TRC(109:6)
           READ XF2
               AT END MOVE 'E' TO TRC(117:1)
           END-READ
           MOVE '--' TO TRC(115:2)
           MOVE XF2-R TO TRC(118:6)
           READ XF2
               AT END MOVE 'E' TO TRC(126:1)
           END-READ
           MOVE '--' TO TRC(124:2)
           MOVE XF2-R TO TRC(127:6)
           READ XF2
               AT END MOVE 'E' TO TRC(135:1)
           END-READ
           MOVE '--' TO TRC(133:2)
           MOVE XF2-R TO TRC(136:6)
           CLOSE XF2
           MOVE '--' TO TRC(142:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 178
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
