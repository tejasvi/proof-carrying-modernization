       IDENTIFICATION DIVISION.
       PROGRAM-ID. RECSUM.
      * Running totals over an input file of amount records.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INFILE
               ORGANIZATION IS RECORD SEQUENTIAL.
           SELECT OUT-FILE ASSIGN TO OUTFILE
               ORGANIZATION IS RECORD SEQUENTIAL.
       DATA DIVISION.
       FILE SECTION.
       FD  IN-FILE.
       01  IN-REC.
           05  IN-ID          PIC X(4).
           05  IN-AMT         PIC S9(5)V99 COMP-3.
       FD  OUT-FILE.
       01  OUT-REC.
           05  OUT-ID         PIC X(4).
           05  OUT-TOTAL      PIC S9(9)V99 COMP-3.
       WORKING-STORAGE SECTION.
       01  WS.
           05  WS-EOF         PIC X VALUE 'N'.
               88  EOF              VALUE 'Y'.
           05  WS-TOTAL       PIC S9(9)V99 COMP-3 VALUE ZERO.
           05  WS-COUNT       PIC 9(5) COMP-3 VALUE ZERO.
       PROCEDURE DIVISION.
       0000-MAIN.
           OPEN INPUT IN-FILE OUTPUT OUT-FILE.
           PERFORM 1000-READ.
           PERFORM 2000-PROCESS UNTIL EOF.
           CLOSE IN-FILE OUT-FILE.
           GOBACK.
       1000-READ.
           READ IN-FILE AT END SET EOF TO TRUE END-READ.
       2000-PROCESS.
           ADD IN-AMT TO WS-TOTAL.
           ADD 1 TO WS-COUNT.
           MOVE IN-ID TO OUT-ID.
           MOVE WS-TOTAL TO OUT-TOTAL.
           WRITE OUT-REC.
           PERFORM 1000-READ.
