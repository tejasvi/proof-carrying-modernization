       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00185.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00185_1.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00185_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS RANDOM
               RECORD KEY IS XF2-K
               ALTERNATE RECORD KEY IS XF2-A
               FILE STATUS IS XF2-S.
           SELECT XF3 ASSIGN TO 'F00185_3.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF3-K
               ALTERNATE RECORD KEY IS XF3-A
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
           05  XF3-K PIC X(3).
           05  XF3-A PIC X(2).
           05  XF3-D PIC X(3).
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(136) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
           05  XF3-S PIC XX VALUE SPACES.
           05  XF3-I PIC X(8) VALUE SPACES.
           05  XF3-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 194.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           MOVE SPACES TO XF3-R
           OPEN OUTPUT XF3
           MOVE XF3-S TO TRC(1:2)
           MOVE 'K01A4CYM' TO XF3-R
           WRITE XF3-R
               NOT INVALID KEY MOVE 'N' TO TRC(6:1)
           END-WRITE
           MOVE XF3-S TO TRC(4:2)
           MOVE 'K08' TO XF2-K
           READ XF2 KEY IS XF2-K
           END-READ
           MOVE XF2-S TO TRC(7:2)
           MOVE XF2-R TO TRC(10:8)
           MOVE 'K05A4PF3' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(18:2)
           MOVE 'K01A4G4N' TO XF3-R
           REWRITE XF3-R
           END-REWRITE
           MOVE XF3-S TO TRC(21:2)
           MOVE 'K07' TO XF2-K
           READ XF2 KEY IS XF2-K
               INVALID KEY MOVE 'E' TO TRC(26:1)
               NOT INVALID KEY MOVE 'N' TO TRC(26:1)
           END-READ
           MOVE XF2-S TO TRC(24:2)
           MOVE XF2-R TO TRC(27:8)
           MOVE 'K08A4ZD3' TO XF3-R
           WRITE XF3-R
           END-WRITE
           MOVE XF3-S TO TRC(35:2)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(38:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(41:2)
           MOVE 'V0GNK9' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(44:2)
           MOVE 'LALMO0' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(47:2)
           OPEN I-O XF3
           MOVE XF3-S TO TRC(50:2)
           MOVE 'K08A17OG' TO XF3-R
           WRITE XF3-R
               NOT INVALID KEY MOVE 'N' TO TRC(55:1)
           END-WRITE
           MOVE XF3-S TO TRC(53:2)
           MOVE 'K04A218I' TO XF3-R
           WRITE XF3-R
               NOT INVALID KEY MOVE 'N' TO TRC(58:1)
           END-WRITE
           MOVE XF3-S TO TRC(56:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(59:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(62:2)
           READ XF1
               AT END MOVE 'E' TO TRC(67:1)
           END-READ
           MOVE XF1-S TO TRC(65:2)
           MOVE XF1-R TO TRC(68:6)
           READ XF1
               AT END MOVE 'E' TO TRC(76:1)
           END-READ
           MOVE XF1-S TO TRC(74:2)
           MOVE XF1-R TO TRC(77:6)
           READ XF1
               AT END MOVE 'E' TO TRC(85:1)
           END-READ
           MOVE XF1-S TO TRC(83:2)
           MOVE XF1-R TO TRC(86:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(92:2)
           CLOSE XF3
           MOVE XF3-S TO TRC(95:2)
           OPEN INPUT XF3
           MOVE XF3-S TO TRC(98:2)
           READ XF3
               AT END MOVE 'E' TO TRC(103:1)
           END-READ
           MOVE XF3-S TO TRC(101:2)
           MOVE XF3-R TO TRC(104:8)
           READ XF3
               AT END MOVE 'E' TO TRC(114:1)
           END-READ
           MOVE XF3-S TO TRC(112:2)
           MOVE XF3-R TO TRC(115:8)
           READ XF3
               AT END MOVE 'E' TO TRC(125:1)
           END-READ
           MOVE XF3-S TO TRC(123:2)
           MOVE XF3-R TO TRC(126:8)
           CLOSE XF3
           MOVE XF3-S TO TRC(134:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 194
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
