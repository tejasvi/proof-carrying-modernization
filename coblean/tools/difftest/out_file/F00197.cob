       IDENTIFICATION DIVISION.
       PROGRAM-ID. F00197.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XF1 ASSIGN TO 'F00197_1.dat'
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
           05  TRC PIC X(138) VALUE SPACES.
           05  XF1-S PIC XX VALUE SPACES.
           05  XF1-I PIC X(8) VALUE SPACES.
           05  XF1-W PIC X(8) VALUE SPACES.
       01  RX REDEFINES R.
           05  BYTE PIC X OCCURS 164.
       01  IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE SPACES TO XF1-R
           OPEN OUTPUT XF1
           MOVE XF1-S TO TRC(1:2)
           READ XF1
               NOT AT END MOVE 'N' TO TRC(6:1)
           END-READ
           MOVE XF1-S TO TRC(4:2)
           MOVE XF1-R TO TRC(7:8)
           MOVE 'K06A5PI2' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(17:1)
               NOT INVALID KEY MOVE 'N' TO TRC(17:1)
           END-WRITE
           MOVE XF1-S TO TRC(15:2)
           MOVE 'K02A3V3W' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(20:1)
           END-WRITE
           MOVE XF1-S TO TRC(18:2)
           MOVE 'K07A3272' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(23:1)
           END-WRITE
           MOVE XF1-S TO TRC(21:2)
           MOVE 'K08A5C44' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(26:1)
               NOT INVALID KEY MOVE 'N' TO TRC(26:1)
           END-WRITE
           MOVE XF1-S TO TRC(24:2)
           MOVE 'K01A4LX7' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(29:1)
               NOT INVALID KEY MOVE 'N' TO TRC(29:1)
           END-WRITE
           MOVE XF1-S TO TRC(27:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(30:2)
           MOVE 'K08A1MF8' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(33:2)
           DELETE XF1 RECORD
           END-DELETE
           MOVE XF1-S TO TRC(36:2)
           MOVE 'K05A6M9T' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(39:2)
           MOVE 'K04A1C3G' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(42:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(45:2)
           OPEN EXTEND XF1
           MOVE XF1-S TO TRC(48:2)
           MOVE 'K07A407S' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(53:1)
           END-WRITE
           MOVE XF1-S TO TRC(51:2)
           MOVE 'K03A2KO3' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(56:1)
           END-WRITE
           MOVE XF1-S TO TRC(54:2)
           MOVE 'K04A30N4' TO XF1-W
           WRITE XF1-R FROM XF1-W
           END-WRITE
           MOVE XF1-S TO TRC(57:2)
           MOVE 'K03A1H8N' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(62:1)
           END-WRITE
           MOVE XF1-S TO TRC(60:2)
           MOVE 'K05A6IBV' TO XF1-W
           WRITE XF1-R FROM XF1-W
               INVALID KEY MOVE 'E' TO TRC(65:1)
           END-WRITE
           MOVE XF1-S TO TRC(63:2)
           READ XF1
               NOT AT END MOVE 'N' TO TRC(68:1)
           END-READ
           MOVE XF1-S TO TRC(66:2)
           MOVE XF1-R TO TRC(69:8)
           MOVE 'K04A55MY' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(77:2)
           MOVE 'K06A4HL1' TO XF1-R
           WRITE XF1-R
           END-WRITE
           MOVE XF1-S TO TRC(80:2)
           MOVE 'K08A2N4E' TO XF1-R
           WRITE XF1-R
               INVALID KEY MOVE 'E' TO TRC(85:1)
               NOT INVALID KEY MOVE 'N' TO TRC(85:1)
           END-WRITE
           MOVE XF1-S TO TRC(83:2)
           CLOSE XF1
           MOVE XF1-S TO TRC(86:2)
           OPEN INPUT XF1
           MOVE XF1-S TO TRC(89:2)
           READ XF1
               AT END MOVE 'E' TO TRC(94:1)
           END-READ
           MOVE XF1-S TO TRC(92:2)
           MOVE XF1-R TO TRC(95:8)
           READ XF1
               AT END MOVE 'E' TO TRC(105:1)
           END-READ
           MOVE XF1-S TO TRC(103:2)
           MOVE XF1-R TO TRC(106:8)
           READ XF1
               AT END MOVE 'E' TO TRC(116:1)
           END-READ
           MOVE XF1-S TO TRC(114:2)
           MOVE XF1-R TO TRC(117:8)
           READ XF1
               AT END MOVE 'E' TO TRC(127:1)
           END-READ
           MOVE XF1-S TO TRC(125:2)
           MOVE XF1-R TO TRC(128:8)
           CLOSE XF1
           MOVE XF1-S TO TRC(136:2)
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 164
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
