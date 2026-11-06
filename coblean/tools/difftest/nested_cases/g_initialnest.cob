      * G-initialnest (GnuCOBOL 3.2): the second CALL of the INITIAL separately compiled program
      * Q18B0 from the contained program Q18B1N stops GnuCOBOL ("attempt to CANCEL active
      * program"). IBM and the model: START B0 01 B0 01 B0 01 END.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q18.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           CALL 'Q18B1'.
           DISPLAY 'END'.
           STOP RUN.
       END PROGRAM Q18.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q18B0 INITIAL.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 K PIC 99 VALUE 1.
       PROCEDURE DIVISION.
           DISPLAY 'B0 ' K.
           ADD 1 TO K.
           EXIT PROGRAM.
       END PROGRAM Q18B0.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q18B1.
       PROCEDURE DIVISION.
           CALL 'Q18B1N'.
           CANCEL 'Q18B0'.
           CALL 'Q18B0'.
           EXIT PROGRAM.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q18B1N.
       PROCEDURE DIVISION.
           CALL 'Q18B0'.
           CALL 'Q18B0'.
           EXIT PROGRAM.
       END PROGRAM Q18B1N.
       END PROGRAM Q18B1.
