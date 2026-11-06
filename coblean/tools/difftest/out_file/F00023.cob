       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00023.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00023_1.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS XF1-K
               FILE STATUS IS XF1-S.
           SELECT XF2 ASSIGN TO 'F00023_2.dat'
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
           05  TRC PIC X(183) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(6) VALUE SPACES.
           05  XF1-W PIC X(6) VALUE SPACES.
           05  XF2-S PIC XX VALUE SPACES.
           05  XF2-I PIC X(8) VALUE SPACES.
           05  XF2-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 223.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           MOVE SPACES TO XF2-R
           OPEN OUTPUT XF2
           MOVE XF2-S TO TRC(1:2)
           MOVE 'K08A2XQS' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(4:2)
           READ XF1
               AT END MOVE 'E' TO TRC(9:1)
           END-READ
           MOVE XF1-S TO TRC(7:2)
           MOVE XF1-R TO TRC(10:6)
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(16:2)
           MOVE 'K03A3Q1R' TO XF2-R
           WRITE XF2-R
           END-WRITE
           MOVE XF2-S TO TRC(19:2)
           MOVE 'K08A12VC' TO XF2-W
           WRITE XF2-R FROM XF2-W
           END-WRITE
           MOVE XF2-S TO TRC(22:2)
           MOVE 'K04V2G' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(25:2)
           MOVE 'K07A1JPO' TO XF2-W
           WRITE XF2-R FROM XF2-W
               INVALID KEY MOVE 'E' TO TRC(30:1)
               NOT INVALID KEY MOVE 'N' TO TRC(30:1)
           END-WRITE
           MOVE XF2-S TO TRC(28:2)
           MOVE 'K06E1I' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(31:2)
           MOVE 'K03A3ANW' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(36:1)
           END-WRITE
           MOVE XF2-S TO TRC(34:2)
           MOVE 'K07Z6K' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(39:1)
           END-WRITE
           MOVE XF1-S TO TRC(37:2)
           OPEN EXTEND XF2
           MOVE XF2-S TO TRC(40:2)
           MOVE 'K087XK' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(45:1)
           END-WRITE
           MOVE XF1-S TO TRC(43:2)
           MOVE 'K01JT3' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(48:1)
               NOT INVALID KEY MOVE 'N' TO TRC(48:1)
           END-WRITE
           MOVE XF1-S TO TRC(46:2)
           MOVE 'K08VWO' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(51:1)
           END-WRITE
           MOVE XF1-S TO TRC(49:2)
           MOVE 'K03NFQ' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(52:2)
           MOVE 'K05A3VCQ' TO XF2-R
           WRITE XF2-R
               INVALID KEY MOVE 'E' TO TRC(57:1)
           END-WRITE
           MOVE XF2-S TO TRC(55:2)
           MOVE 'K03UOQ' TO XF1-R
           WRITE XF1-R
               NOT INVALID KEY MOVE 'N' TO TRC(60:1)
           END-WRITE
           MOVE XF1-S TO TRC(58:2)
           MOVE 'K04P3Z' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(63:1)
               NOT INVALID KEY MOVE 'N' TO TRC(63:1)
           END-WRITE
           MOVE XF1-S TO TRC(61:2)
           MOVE 'K08EL6' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(66:1)
           END-WRITE
           MOVE XF1-S TO TRC(64:2)
           READ XF2
               AT END MOVE 'E' TO TRC(69:1)
               NOT AT END MOVE 'N' TO TRC(69:1)
           END-READ
           MOVE XF2-S TO TRC(67:2)
           MOVE XF2-R TO TRC(70:8)
           OPEN EXTEND XF2
           MOVE XF2-S TO TRC(78:2)
           OPEN I-O XF2
           MOVE XF2-S TO TRC(81:2)
           MOVE 'K08FUI' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(86:1)
               NOT INVALID KEY MOVE 'N' TO TRC(86:1)
           END-WRITE
           MOVE XF1-S TO TRC(84:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(87:2)
           READ XF1
           END-READ
           MOVE XF1-S TO TRC(90:2)
           MOVE XF1-R TO TRC(93:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(99:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(102:2)
           READ XF1
               AT END MOVE 'E' TO TRC(107:1)
           END-READ
           MOVE XF1-S TO TRC(105:2)
           MOVE XF1-R TO TRC(108:6)
           READ XF1
               AT END MOVE 'E' TO TRC(116:1)
           END-READ
           MOVE XF1-S TO TRC(114:2)
           MOVE XF1-R TO TRC(117:6)
           READ XF1
               AT END MOVE 'E' TO TRC(125:1)
           END-READ
           MOVE XF1-S TO TRC(123:2)
           MOVE XF1-R TO TRC(126:6)
           READ XF1
               AT END MOVE 'E' TO TRC(134:1)
           END-READ
           MOVE XF1-S TO TRC(132:2)
           MOVE XF1-R TO TRC(135:6)
           READ XF1
               AT END MOVE 'E' TO TRC(143:1)
           END-READ
           MOVE XF1-S TO TRC(141:2)
           MOVE XF1-R TO TRC(144:6)
           CLOSE XF1
           MOVE XF1-S TO TRC(150:2)
           CLOSE XF2
           MOVE XF2-S TO TRC(153:2)
           OPEN INPUT XF2
           MOVE XF2-S TO TRC(156:2)
           READ XF2
               AT END MOVE 'E' TO TRC(161:1)
           END-READ
           MOVE XF2-S TO TRC(159:2)
           MOVE XF2-R TO TRC(162:8)
           READ XF2
               AT END MOVE 'E' TO TRC(172:1)
           END-READ
           MOVE XF2-S TO TRC(170:2)
           MOVE XF2-R TO TRC(173:8)
           CLOSE XF2
           MOVE XF2-S TO TRC(181:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 223
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
