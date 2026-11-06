      * EXTERNAL record shared by a batch program and a nested program with other subordinate
      * items; CANCEL of a batch program; an INITIAL nested program.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q3.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 EX1 EXTERNAL.
          05 EX1A PIC X(4).
          05 EX1B PIC 99.
       01 W1 PIC 99 VALUE 0.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE 'abcd' TO EX1A.
           MOVE 42 TO EX1B.
           CALL 'Q3B'.
           DISPLAY 'Q3 ' EX1A ' ' EX1B.
           CALL 'Q3N'.
           DISPLAY 'Q3 ' EX1A ' ' EX1B.
           CALL 'Q3B'.
           DISPLAY 'RC '.
           CALL 'Q3C'.
           DISPLAY 'RC '.
           CALL 'Q3C'.
           CANCEL 'Q3C'.
           CALL 'Q3C'.
           CALL 'Q3I'.
           CALL 'Q3I'.
           STOP RUN.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q3N.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 EX1 EXTERNAL.
          05 EX1X PIC X(6).
       PROCEDURE DIVISION.
           DISPLAY 'Q3N ' EX1X.
           MOVE 'nested' TO EX1X.
       END PROGRAM Q3N.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q3I IS INITIAL.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 C1 PIC 99 VALUE 1.
       01 C2 PIC 99 VALUE 0.
       01 C3 PIC X(3) VALUE SPACES.
       PROCEDURE DIVISION.
           DISPLAY 'Q3I ' C1 ' ' C2 ' [' C3 ']'.
           ADD 1 TO C1.
           MOVE 9 TO C2.
           MOVE 'zzz' TO C3.
       END PROGRAM Q3I.
       END PROGRAM Q3.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q3B.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 EX1 EXTERNAL.
          05 EX1C PIC X(2).
          05 EX1D PIC X(4).
       PROCEDURE DIVISION.
           DISPLAY 'Q3B ' EX1C ' ' EX1D ' '.
           MOVE 'QB' TO EX1C.
           GOBACK.
       END PROGRAM Q3B.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q3C.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 K1 PIC 99 VALUE 1.
       01 K2 PIC 99 VALUE 0.
       01 K3 PIC X(3) VALUE SPACES.
       PROCEDURE DIVISION.
           DISPLAY 'Q3C ' K1 ' ' K2 ' [' K3 '] '.
           ADD 1 TO K1.
           MOVE 9 TO K2.
           MOVE 'zzz' TO K3.
           GOBACK.
       END PROGRAM Q3C.
