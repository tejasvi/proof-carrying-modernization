      * CANCEL of a nested program (and of the program it contains), by literal and identifier.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q10.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 PN PIC X(8) VALUE 'Q10C'.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           CALL 'Q10C'.
           CALL 'Q10C'.
           CANCEL 'Q10C'.
           CALL 'Q10C'.
           CANCEL PN.
           CALL PN.
           CALL 'Q10C'.
           STOP RUN.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q10C.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 K PIC 99 VALUE 1.
       PROCEDURE DIVISION.
           DISPLAY 'Q10C ' K.
           ADD 1 TO K.
           CALL 'Q10D'.
           EXIT PROGRAM.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q10D.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 K PIC 99 VALUE 50.
       PROCEDURE DIVISION.
           DISPLAY 'Q10D ' K.
           ADD 1 TO K.
           EXIT PROGRAM.
       END PROGRAM Q10D.
       END PROGRAM Q10C.
       END PROGRAM Q10.
