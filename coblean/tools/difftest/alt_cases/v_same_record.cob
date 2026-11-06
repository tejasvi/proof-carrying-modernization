       IDENTIFICATION DIVISION.
       PROGRAM-ID. P3.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT XA ASSIGN TO "p3a.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS KA FILE STATUS IS SA.
           SELECT XB ASSIGN TO "p3b.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS KB FILE STATUS IS SB.
           SELECT XC ASSIGN TO "p3c.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS KC FILE STATUS IS SC.
           SELECT XD ASSIGN TO "p3d.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
               RECORD KEY IS KD FILE STATUS IS SD1.
           SELECT XE ASSIGN TO "p3e.dat"
               ORGANIZATION IS SEQUENTIAL FILE STATUS IS SE.
           SELECT XF ASSIGN TO "p3f.dat"
               ORGANIZATION IS SEQUENTIAL FILE STATUS IS SF.
       I-O-CONTROL.
           SAME AREA FOR XA XB
           SAME RECORD AREA FOR XC, XD
           SAME XE XF.
       DATA DIVISION.
       FILE SECTION.
       FD XA.
       01 RA.
          05 KA PIC X(3).
          05 VA PIC X(5).
       FD XB.
       01 RB.
          05 KB PIC X(3).
          05 VB PIC X(7).
       FD XC.
       01 RC.
          05 KC PIC X(3).
          05 VC PIC X(5).
       FD XD.
       01 RX.
          05 KD PIC X(3).
          05 VD PIC X(7).
       01 RX2 PIC X(4).
       FD XE.
       01 RE PIC X(6).
       FD XF.
       01 RG PIC X(6).
       WORKING-STORAGE SECTION.
       01 SA PIC XX VALUE "..".
       01 SB PIC XX VALUE "..".
       01 SC PIC XX VALUE "..".
       01 SD1 PIC XX VALUE "..".
       01 SE PIC XX VALUE "..".
       01 SF PIC XX VALUE "..".
       PROCEDURE DIVISION.
       MAIN.
           MOVE "AAAaaaaa" TO RA.
           DISPLAY "1 RA=" RA " RB=" RB.
           MOVE "BBBbbbbbbb" TO RB.
           DISPLAY "2 RA=" RA " RB=" RB.
           MOVE "CCCccccc" TO RC.
           DISPLAY "3 RC=" RC " RX=" RX " RX2=" RX2.
           MOVE "DDDddddddd" TO RX.
           DISPLAY "4 RC=" RC " RX=" RX " RX2=" RX2.
           MOVE "eeeeee" TO RE.
           DISPLAY "5 RE=" RE " RG=" RG.
           OPEN OUTPUT XC.
           OPEN OUTPUT XD.
           MOVE "K01ccccc" TO RC. WRITE RC.
           DISPLAY "6 " SC " RC=" RC " RX=" RX.
           MOVE "K02ddddddd" TO RX. WRITE RX.
           DISPLAY "7 " SD1 " RC=" RC " RX=" RX.
           CLOSE XC XD.
           OPEN INPUT XC XD.
           READ XC NEXT RECORD.
           DISPLAY "8 " SC " RC=" RC " RX=" RX.
           READ XD NEXT RECORD.
           DISPLAY "9 " SD1 " RC=" RC " RX=" RX.
           CLOSE XC XD.
           STOP RUN.
