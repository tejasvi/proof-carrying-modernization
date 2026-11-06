      * G-varying (GnuCOBOL 3.2 deviations, model = IBM): variable-length
      * records (RECORD VARYING ... DEPENDING ON).  W4: a length above
      * the maximum is a boundary violation (IBM 44, nothing written);
      * GnuCOBOL writes the maximum length (00).  R1: READ INTO moves
      * the record read (12 bytes, padded with spaces: IBM "the size of
      * the current record is determined by the RECORD clause");
      * GnuCOBOL moves the whole record area (12 A + 28 stale D).
      * R3/R4 differ as a consequence of W4.  U2: REWRITE of a sequential
      * record with its own length (12) succeeds on IBM (only a length
      * change is a boundary violation); GnuCOBOL gives 44.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VLR1.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT VF ASSIGN TO 'vlr1.dat'
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS FS1.
       DATA DIVISION.
       FILE SECTION.
       FD  VF
           RECORD IS VARYING IN SIZE FROM 10 TO 40
           DEPENDING ON RLEN.
       01  V-REC PIC X(40).
       WORKING-STORAGE SECTION.
       01  FS1 PIC XX.
       01  RLEN PIC 9(4).
       01  BUF PIC X(40).
       PROCEDURE DIVISION.
           OPEN OUTPUT VF
           MOVE ALL 'A' TO V-REC
           MOVE 12 TO RLEN
           WRITE V-REC
           DISPLAY 'W1 ' FS1
           MOVE ALL 'B' TO V-REC
           MOVE 40 TO RLEN
           WRITE V-REC
           DISPLAY 'W2 ' FS1
           MOVE ALL 'C' TO V-REC
           MOVE 5 TO RLEN
           WRITE V-REC
           DISPLAY 'W3 ' FS1
           MOVE 41 TO RLEN
           WRITE V-REC
           DISPLAY 'W4 ' FS1
           MOVE ALL 'D' TO V-REC
           MOVE 10 TO RLEN
           WRITE V-REC
           DISPLAY 'W5 ' FS1
           CLOSE VF
           OPEN INPUT VF
           MOVE ALL '*' TO BUF
           MOVE 0 TO RLEN
           READ VF INTO BUF
           DISPLAY 'R1 ' FS1 ' ' RLEN ' ' BUF
           MOVE ALL '*' TO BUF
           READ VF INTO BUF
           DISPLAY 'R2 ' FS1 ' ' RLEN ' ' BUF
           MOVE ALL '*' TO BUF
           READ VF INTO BUF
           DISPLAY 'R3 ' FS1 ' ' RLEN ' ' BUF
           READ VF
           DISPLAY 'R4 ' FS1 ' ' RLEN
           CLOSE VF
           OPEN I-O VF
           READ VF
           DISPLAY 'U1 ' FS1 ' ' RLEN
           MOVE ALL 'E' TO V-REC
           REWRITE V-REC
           DISPLAY 'U2 ' FS1
           CLOSE VF
           STOP RUN.
