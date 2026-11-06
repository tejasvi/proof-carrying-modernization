      * G-cancelinitial (GnuCOBOL 3.2): Q21B1 cancels the INITIAL program Q21B0, which the main
      * program called and which has returned: GnuCOBOL stops with "attempt to CANCEL active
      * program". IBM and the model: START B0 01 B0 01 B1 END.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q21.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           CALL 'Q21B0'.
           CANCEL 'Q21B0'.
           CALL 'Q21B0'.
           CALL 'Q21B1'.
           DISPLAY 'END'.
           STOP RUN.
       END PROGRAM Q21.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q21B0 INITIAL.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 K PIC 99 VALUE 1.
       PROCEDURE DIVISION.
           DISPLAY 'B0 ' K.
           ADD 1 TO K.
           EXIT PROGRAM.
       END PROGRAM Q21B0.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q21B1.
       PROCEDURE DIVISION.
           CANCEL 'Q21B0'.
           DISPLAY 'B1'.
           EXIT PROGRAM.
       END PROGRAM Q21B1.
