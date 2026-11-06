       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00038.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00038_1.dat'
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
           05  TRC PIC X(74) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 100.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           OPEN I-O XF1
           MOVE XF1-S TO TRC(4:2)
           MOVE 'K08A3R9C' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(9:1)
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF1-S TO TRC(7:2)
           MOVE 'K05A55OQ' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(12:1)
           END-WRITE
           MOVE XF1-S TO TRC(10:2)
           READ XF1
               AT END MOVE 'E' TO TRC(15:1)
           END-READ
           MOVE XF1-S TO TRC(13:2)
           MOVE XF1-R TO TRC(16:8)
           MOVE 'K08A57JR' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(24:2)
           READ XF1
               AT END MOVE 'E' TO TRC(29:1)
           END-READ
           MOVE XF1-S TO TRC(27:2)
           MOVE XF1-R TO TRC(30:8)
           MOVE 'K06A2G7A' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(40:1)
           END-WRITE
           MOVE XF1-S TO TRC(38:2)
           MOVE 'K06A2PGN' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(41:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(44:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(47:2)
           READ XF1
               AT END MOVE 'E' TO TRC(52:1)
           END-READ
           MOVE XF1-S TO TRC(50:2)
           MOVE XF1-R TO TRC(53:8)
           READ XF1
               AT END MOVE 'E' TO TRC(63:1)
           END-READ
           MOVE XF1-S TO TRC(61:2)
           MOVE XF1-R TO TRC(64:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(72:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 100
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
