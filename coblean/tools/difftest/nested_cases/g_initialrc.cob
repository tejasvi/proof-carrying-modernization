      * G-initialrc (GnuCOBOL 3.2): after a CALL of the INITIAL separately compiled program
      * Q13B, which sets RETURN-CODE to 4 on every call, GnuCOBOL shows 0 in the caller. IBM
      * (RETURN-CODE: the value is passed to the calling program) and the model: M1 0004,
      * C1 0004, M2 0004.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q13.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 RCED PIC -9(4).
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           CALL 'Q13B'.
           MOVE RETURN-CODE TO RCED.
           DISPLAY 'M1 ' RCED.
           CALL 'Q13C'.
           MOVE RETURN-CODE TO RCED.
           DISPLAY 'M2 ' RCED.
           MOVE 0 TO RETURN-CODE.
           STOP RUN.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q13C.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 RCED PIC -9(4).
       PROCEDURE DIVISION.
           MOVE 7 TO RETURN-CODE.
           CALL 'Q13B'.
           MOVE RETURN-CODE TO RCED.
           DISPLAY 'C1 ' RCED.
           EXIT PROGRAM.
       END PROGRAM Q13C.
       END PROGRAM Q13.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q13B INITIAL.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 K PIC 9 VALUE 3.
       PROCEDURE DIVISION.
           ADD 1 TO K.
           MOVE K TO RETURN-CODE.
           GOBACK.
       END PROGRAM Q13B.
