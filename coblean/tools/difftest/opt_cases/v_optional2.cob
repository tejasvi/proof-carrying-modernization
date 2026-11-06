      * ABSENT: 1,2,3
      * Absent OPTIONAL indexed files: START as the first statement after
      * OPEN INPUT, keyed READ and READ NEXT after OPEN I-O created the
      * file, ACCESS SEQUENTIAL READs: agrees with GnuCOBOL.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VOPT2.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT OPTIONAL XC ASSIGN TO "qc.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS KC FILE STATUS IS TC.
           SELECT OPTIONAL XD ASSIGN TO "qd.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS KD FILE STATUS IS TD.
           SELECT OPTIONAL XF ASSIGN TO "qf.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS KF FILE STATUS IS TF.
       DATA DIVISION.
       FILE SECTION.
       FD XC.
       01 QC.
          05 KC PIC X(3).
          05 VC PIC X(5).
       FD XD.
       01 QD.
          05 KD PIC X(3).
          05 VD PIC X(5).
       FD XF.
       01 QF.
          05 KF PIC X(3).
          05 VF PIC X(5).
       WORKING-STORAGE SECTION.
       01 TC PIC XX VALUE "..".
       01 TD PIC XX VALUE "..".
       01 TF PIC XX VALUE "..".
       PROCEDURE DIVISION.
       M0.
           OPEN INPUT XC DISPLAY "C1 OPEN INPUT " TC
           MOVE "K01" TO KC
           START XC KEY = KC INVALID KEY DISPLAY "C2 INVALID KEY"
           END-START
           DISPLAY "C2 START " TC
           READ XC NEXT DISPLAY "C3 READ NEXT " TC
           READ XC NEXT DISPLAY "C4 READ NEXT " TC
           READ XC DISPLAY "C5 READ KEY " TC
           CLOSE XC
           OPEN I-O XD DISPLAY "D1 OPEN I-O " TD
           MOVE "K01" TO KD
           READ XD DISPLAY "D2 READ KEY " TD
           READ XD NEXT DISPLAY "D3 READ NEXT " TD
           MOVE "K07" TO KD MOVE "DDDDD" TO VD
           WRITE QD DISPLAY "D4 WRITE " TD
           CLOSE XD
           OPEN INPUT XD DISPLAY "D5 OPEN INPUT " TD
           READ XD NEXT DISPLAY "D6 READ NEXT " TD " " QD
           READ XD NEXT DISPLAY "D7 READ NEXT " TD
           CLOSE XD
           OPEN INPUT XF DISPLAY "F1 OPEN INPUT " TF
           READ XF DISPLAY "F2 READ " TF
           READ XF DISPLAY "F3 READ " TF
           CLOSE XF
           OPEN EXTEND XF DISPLAY "F4 OPEN EXTEND " TF
           MOVE "K02" TO KF MOVE "FFFFF" TO VF
           WRITE QF DISPLAY "F5 WRITE " TF
           CLOSE XF
           OPEN INPUT XF DISPLAY "F6 OPEN INPUT " TF
           READ XF DISPLAY "F7 READ " TF " " QF
           CLOSE XF
           STOP RUN.
