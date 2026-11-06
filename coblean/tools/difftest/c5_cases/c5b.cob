       IDENTIFICATION DIVISION.
       PROGRAM-ID. C5B.
      * RECORD VARYING DEPENDING ON without FROM or TO; the second
      * record is the longer one, so the record area and the maximum
      * record length are the second record's; WRITE writes REC-LEN
      * bytes and READ sets REC-LEN to the length read.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO 'C5BF'
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS FS1.
       DATA DIVISION.
       FILE SECTION.
       FD F1
           RECORD VARYING DEPENDING ON REC-LEN.
       01 SHORT-REC PIC X(10).
       01 LONG-REC.
          05 LONG-A PIC X(10).
          05 LONG-B PIC X(15).
       WORKING-STORAGE SECTION.
       01 FS1 PIC XX.
       01 REC-LEN PIC 9(4) COMP.
       01 W PIC X(30).
       01 D-LEN PIC 9(4).
       PROCEDURE DIVISION.
       P0.
           OPEN OUTPUT F1
           DISPLAY 'O ' FS1 '|'
           MOVE 'SHORT-0001' TO SHORT-REC
           MOVE 10 TO REC-LEN
           WRITE SHORT-REC
           DISPLAY 'W1 ' FS1 '|'
           MOVE 'LONG--0002' TO LONG-A
           MOVE 'BBBBBBBBBBBBBBB' TO LONG-B
           MOVE 25 TO REC-LEN
           WRITE LONG-REC
           DISPLAY 'W2 ' FS1 '|'
           MOVE 'LONG--0003' TO LONG-A
           MOVE 'CCCCCCCCCCCCCCC' TO LONG-B
           MOVE 18 TO REC-LEN
           WRITE LONG-REC
           DISPLAY 'W3 ' FS1 '|'
           CLOSE F1
           OPEN INPUT F1
           MOVE ALL '*' TO W
           MOVE 0 TO REC-LEN
           READ F1 INTO W
           MOVE REC-LEN TO D-LEN
           DISPLAY 'R1 ' FS1 ' ' D-LEN ' ' W '|'
           MOVE ALL '*' TO W
           MOVE 0 TO REC-LEN
           READ F1 INTO W
           MOVE REC-LEN TO D-LEN
           DISPLAY 'R2 ' FS1 ' ' D-LEN ' ' W '|'
           MOVE ALL '*' TO W
           MOVE 0 TO REC-LEN
           READ F1 INTO W
           MOVE REC-LEN TO D-LEN
           DISPLAY 'R3 ' FS1 ' ' D-LEN ' ' W '|'
           READ F1 INTO W
           DISPLAY 'R4 ' FS1 '|'
           CLOSE F1
           STOP RUN.
