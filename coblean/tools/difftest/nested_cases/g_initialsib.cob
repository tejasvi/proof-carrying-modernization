      * G-initialsib (GnuCOBOL 3.2): calling the INITIAL contained program Q19C0 resets Q19C1N,
      * a program contained in its sibling Q19C1. IBM and the model: START C1N 01 C0 C1N 02 END.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q19.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           CALL 'Q19C1'.
           CALL 'Q19C0'.
           CALL 'Q19C1'.
           DISPLAY 'END'.
           STOP RUN.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q19C0 INITIAL.
       PROCEDURE DIVISION.
           DISPLAY 'C0'.
           EXIT PROGRAM.
       END PROGRAM Q19C0.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q19C1.
       PROCEDURE DIVISION.
           CALL 'Q19C1N'.
           EXIT PROGRAM.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q19C1N IS COMMON.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 K PIC 99 VALUE 1.
       PROCEDURE DIVISION.
           DISPLAY 'C1N ' K.
           ADD 1 TO K.
           EXIT PROGRAM.
       END PROGRAM Q19C1N.
       END PROGRAM Q19C1.
       END PROGRAM Q19.
