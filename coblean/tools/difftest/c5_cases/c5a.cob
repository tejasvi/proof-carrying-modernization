       IDENTIFICATION DIVISION.
       PROGRAM-ID. C5A.
      * Two record descriptions of different lengths, no RECORD
      * clause: a variable-length file, record area as long as the
      * longest record; WRITE writes the named record's length.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO 'C5AF'
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS FS1.
       DATA DIVISION.
       FILE SECTION.
       FD F1.
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
           MOVE 'SHORT-0001' TO SHORT-REC
           WRITE SHORT-REC
           DISPLAY 'W1 ' FS1 '|'
           MOVE 'LONG--0002' TO LONG-A
           MOVE 'BBBBBBBBBBBBBBB' TO LONG-B
           WRITE LONG-REC
           DISPLAY 'W2 ' FS1 '|'
           MOVE 'SHORT-0003' TO SHORT-REC
           WRITE SHORT-REC
           DISPLAY 'W3 ' FS1 '|'
           CLOSE F1
           OPEN INPUT F1
           MOVE ALL '*' TO W
           READ F1 INTO W
           DISPLAY 'R1 ' FS1 ' ' W '|'
           MOVE ALL '*' TO W
           READ F1 INTO W
           DISPLAY 'R2 ' FS1 ' ' W '|'
           MOVE ALL '*' TO W
           READ F1 INTO W
           DISPLAY 'R3 ' FS1 ' ' W '|'
           MOVE ALL '*' TO W
           READ F1 INTO W
           DISPLAY 'R4 ' FS1 '|'
           CLOSE F1
           STOP RUN.
