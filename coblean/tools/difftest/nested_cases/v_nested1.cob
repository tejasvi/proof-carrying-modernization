      * Nested programs: GLOBAL data, condition name and index seen and set in contained
      * programs, a local name hiding a global one, a COMMON program called by its parent, a
      * sibling and a program nested in a sibling, CALL identifier of a nested program.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 G1 GLOBAL PIC X(4) VALUE 'G1G1'.
       01 G2 GLOBAL.
          05 G2A PIC 99 VALUE 10.
             88 G2-TEN VALUE 10.
          05 G2T PIC X OCCURS 3 INDEXED BY GX.
       01 L1 PIC X(4) VALUE 'L1L1'.
       01 HID GLOBAL PIC X(4) VALUE 'HHHH'.
       01 PN PIC X(8) VALUE 'Q1B'.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE 'abc' TO G2T(1) G2T(2) G2T(3).
           SET GX TO 2.
           CALL 'Q1A'.
           DISPLAY G1 ' ' G2A ' ' HID.
           CALL PN.
           DISPLAY G1 ' ' G2A.
           CALL 'Q1C'.
           DISPLAY 'END'.
           STOP RUN.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q1A.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 HID PIC X(4) VALUE 'aaaa'.
       PROCEDURE DIVISION.
           DISPLAY 'Q1A ' G1 ' ' G2A ' ' HID ' ' G2T(GX).
           IF G2-TEN DISPLAY 'TEN' END-IF.
           MOVE 'XXXX' TO G1.
           MOVE 11 TO G2A.
           MOVE 'bbbb' TO HID.
           CALL 'Q1B'.
           EXIT PROGRAM.
       END PROGRAM Q1A.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q1B IS COMMON.
       PROCEDURE DIVISION.
           DISPLAY 'Q1B ' G1 ' ' G2A.
           MOVE 'YYYY' TO G1.
           ADD 1 TO G2A.
           GOBACK.
       END PROGRAM Q1B.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q1C.
       PROCEDURE DIVISION.
           DISPLAY 'Q1C ' G1.
           CALL 'Q1D'.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q1D.
       PROCEDURE DIVISION.
           DISPLAY 'Q1D ' G1.
           CALL 'Q1B'.
       END PROGRAM Q1D.
       END PROGRAM Q1C.
       END PROGRAM Q1.
