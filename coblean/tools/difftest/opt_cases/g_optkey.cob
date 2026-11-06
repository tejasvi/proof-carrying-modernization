      * ABSENT: 1,2,3
      * G-optkey: the first READ of an absent OPTIONAL file opened INPUT
      * is a keyed READ. GnuCOBOL 3.2: 10 without the INVALID KEY phrase,
      * then READ NEXT 46. IBM (file status 23: "a START or random READ
      * statement was attempted on an optional input file that was
      * unavailable"): 23 and the INVALID KEY phrase, then 10. The model
      * follows IBM. Later keyed READs: 23 on both.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GOPTKEY.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT OPTIONAL XA ASSIGN TO "qa.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS RANDOM
               RECORD KEY IS KA FILE STATUS IS TA.
           SELECT OPTIONAL XB ASSIGN TO "qb.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS KB FILE STATUS IS TB.
           SELECT OPTIONAL XE ASSIGN TO "qe.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS RANDOM
               RECORD KEY IS KE FILE STATUS IS TE.
       DATA DIVISION.
       FILE SECTION.
       FD XA.
       01 QA.
          05 KA PIC X(3).
          05 VA PIC X(5).
       FD XB.
       01 QB.
          05 KB PIC X(3).
          05 VB PIC X(5).
       FD XE.
       01 QE.
          05 KE PIC X(3).
          05 VE PIC X(5).
       WORKING-STORAGE SECTION.
       01 TA PIC XX VALUE "..".
       01 TB PIC XX VALUE "..".
       01 TE PIC XX VALUE "..".
       PROCEDURE DIVISION.
       M0.
           OPEN INPUT XA DISPLAY "A1 OPEN INPUT " TA
           MOVE "K01" TO KA
           READ XA INVALID KEY DISPLAY "A2 INVALID KEY" END-READ
           DISPLAY "A2 READ KEY " TA
           READ XA INVALID KEY DISPLAY "A3 INVALID KEY" END-READ
           DISPLAY "A3 READ KEY " TA
           CLOSE XA DISPLAY "A4 CLOSE " TA
           OPEN INPUT XA DISPLAY "A5 OPEN INPUT " TA
           READ XA DISPLAY "A6 READ KEY " TA
           CLOSE XA
           OPEN INPUT XB DISPLAY "B1 OPEN INPUT " TB
           MOVE "K01" TO KB
           READ XB INVALID KEY DISPLAY "B2 INVALID KEY" END-READ
           DISPLAY "B2 READ KEY " TB
           READ XB NEXT AT END DISPLAY "B3 AT END" END-READ
           DISPLAY "B3 READ NEXT " TB
           READ XB NEXT DISPLAY "B4 READ NEXT " TB
           CLOSE XB
           OPEN INPUT XE DISPLAY "E1 OPEN INPUT " TE
           MOVE "K01" TO KE
           WRITE QE DISPLAY "E2 WRITE " TE
           DELETE XE DISPLAY "E3 DELETE " TE
           READ XE DISPLAY "E4 READ KEY " TE
           READ XE DISPLAY "E5 READ KEY " TE
           CLOSE XE
           STOP RUN.
