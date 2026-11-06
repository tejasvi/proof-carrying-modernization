       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00076.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00076_1.dat'
               ORGANIZATION IS SEQUENTIAL
               ACCESS MODE IS SEQUENTIAL
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00076_2.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF2-K
               ALTERNATE RECORD KEY IS XF2-A
               FILE STATUS IS XF2-S.
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
       WORKING-STORAGE SECTION.
       01  R.
           05  SENT PIC X(8) VALUE 'FTRACE01'.
           05  TRC PIC X(173) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 213.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           CLOSE XF1
           MOVE XF1-S TO TRC(1:2)
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(4:2)
           MOVE 'K08A4FJF' TO XF2-R
           WRITE XF2-R
               NOT INVALID KEY MOVE 'N' TO TRC(9:1)
           END-WRITE
           MOVE XF2-S TO TRC(7:2)
           MOVE 'K08A4U4I' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(12:1)
           END-WRITE
           MOVE XF2-S TO TRC(10:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(13:2)
           READ XF2
               AT END MOVE 'E' TO TRC(18:1)
           END-READ
           MOVE XF2-S TO TRC(16:2)
           MOVE XF2-R TO TRC(19:8)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(27:2)
           MOVE '6JDWKC' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(30:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(33:2)
           MOVE 'K08A3YPI' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(38:1)
           END-WRITE
           MOVE XF2-S TO TRC(36:2)
           MOVE 'K07A3TTY' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(41:1)
           END-WRITE
           MOVE XF2-S TO TRC(39:2)
           MOVE 'K05A5RGB' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(44:1)
           END-WRITE
           MOVE XF2-S TO TRC(42:2)
           MOVE '2UCK3Z' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(45:2)
           MOVE 'K08A2BUL' TO XF2-W
           WRITE XF2-R FROM XF2-W
               NOT INVALID KEY MOVE 'N' TO TRC(50:1)
           END-WRITE
           MOVE XF2-S TO TRC(48:2)
           MOVE 'K03A664H' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(51:2)
           MOVE 'PNPOQP' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(54:2)
           MOVE 'K01A18SW' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(59:1)
           END-WRITE
           MOVE XF2-S TO TRC(57:2)
           MOVE 'XWV966' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(60:2)
           READ XF2 NEXT RECORD
           END-READ
           MOVE XF2-S TO TRC(63:2)
           MOVE XF2-R TO TRC(66:8)
           MOVE 'K06A2YES' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(74:2)
           MOVE '5ORF15' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(77:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(80:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(83:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(86:2)
           READ XF1
               AT END MOVE 'E' TO TRC(91:1)
           END-READ
           MOVE XF1-S TO TRC(89:2)
           MOVE XF1-R TO TRC(92:6)
           READ XF1
               AT END MOVE 'E' TO TRC(100:1)
           END-READ
           MOVE XF1-S TO TRC(98:2)
           MOVE XF1-R TO TRC(101:6)
           READ XF1
               AT END MOVE 'E' TO TRC(109:1)
           END-READ
           MOVE XF1-S TO TRC(107:2)
           MOVE XF1-R TO TRC(110:6)
           READ XF1
               AT END MOVE 'E' TO TRC(118:1)
           END-READ
           MOVE XF1-S TO TRC(116:2)
           MOVE XF1-R TO TRC(119:6)
           READ XF1
               AT END MOVE 'E' TO TRC(127:1)
           END-READ
           MOVE XF1-S TO TRC(125:2)
           MOVE XF1-R TO TRC(128:6)
           READ XF1
               AT END MOVE 'E' TO TRC(136:1)
           END-READ
           MOVE XF1-S TO TRC(134:2)
           MOVE XF1-R TO TRC(137:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(143:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(146:2)
           READ XF2
               AT END MOVE 'E' TO TRC(151:1)
           END-READ
           MOVE XF2-S TO TRC(149:2)
           MOVE XF2-R TO TRC(152:8)
           READ XF2
               AT END MOVE 'E' TO TRC(162:1)
           END-READ
           MOVE XF2-S TO TRC(160:2)
           MOVE XF2-R TO TRC(163:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(171:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 213
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
