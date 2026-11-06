       IDENTIFICATION DIVISION.
       PROGRAM-ID. C5C.
      * RECORD CONTAINS 10 TO 25 CHARACTERS with the shorter record
      * first: the record area is the longer record (25 bytes), not
      * the first one; both lengths are written and read back.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO 'C5CF'
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS FS1.
       DATA DIVISION.
       FILE SECTION.
       FD F1
           RECORD CONTAINS 10 TO 25 CHARACTERS.
       01 SHORT-REC PIC X(10).
       01 LONG-REC.
          05 LONG-A PIC X(10).
          05 LONG-B PIC X(15).
       WORKING-STORAGE SECTION.
       01 FS1 PIC XX.
       01 W PIC X(30).
       PROCEDURE DIVISION.
       P0.
           OPEN OUTPUT F1
           DISPLAY 'O ' FS1 '|'
           MOVE 'LONG--0001' TO LONG-A
           MOVE 'BBBBBBBBBBBBBBB' TO LONG-B
           WRITE LONG-REC
           DISPLAY 'W1 ' FS1 '|'
           MOVE 'SHORT-0002' TO SHORT-REC
           WRITE SHORT-REC
           DISPLAY 'W2 ' FS1 '|'
           CLOSE F1
           OPEN INPUT F1
           MOVE ALL '*' TO W
           READ F1 INTO W
           DISPLAY 'R1 ' FS1 ' ' W '|'
           MOVE ALL '*' TO W
           READ F1 INTO W
           DISPLAY 'R2 ' FS1 ' ' W '|'
           READ F1 INTO W
           DISPLAY 'R3 ' FS1 '|'
           CLOSE F1
           STOP RUN.
