      * Variable-length records where IBM and GnuCOBOL agree: WRITE of
      * lengths in range (12, 40, 10) and below the minimum (5: 44),
      * READ sets the DEPENDING ON item, the record area holds the
      * record read (shown as V-REC(1:RLEN)), REWRITE with a different
      * length is 44 (same-length REWRITE: see g_varying.cob).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VLR2.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT VF ASSIGN TO 'vlr2.dat'
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
           MOVE ALL 'D' TO V-REC
           MOVE 10 TO RLEN
           WRITE V-REC
           DISPLAY 'W4 ' FS1
           CLOSE VF
           OPEN INPUT VF
           MOVE 0 TO RLEN
           READ VF
           DISPLAY 'R1 ' FS1 ' ' RLEN ' ' V-REC(1:RLEN)
           READ VF
           DISPLAY 'R2 ' FS1 ' ' RLEN ' ' V-REC(1:RLEN)
           READ VF
           DISPLAY 'R3 ' FS1 ' ' RLEN ' ' V-REC(1:RLEN)
           READ VF
           DISPLAY 'R4 ' FS1 ' ' RLEN
           CLOSE VF
           OPEN I-O VF
           READ VF
           DISPLAY 'U1 ' FS1 ' ' RLEN
           READ VF
           DISPLAY 'U3 ' FS1 ' ' RLEN
           MOVE 12 TO RLEN
           REWRITE V-REC
           DISPLAY 'U4 ' FS1
           CLOSE VF
           OPEN INPUT VF
           READ VF
           DISPLAY 'X1 ' FS1 ' ' RLEN ' ' V-REC(1:RLEN)
           READ VF
           DISPLAY 'X2 ' FS1 ' ' RLEN ' ' V-REC(1:RLEN)
           CLOSE VF
           STOP RUN.
