      * G-cancelcommon (GnuCOBOL 3.2): Q12C2N, contained in Q12C2, cancels the COMMON program
      * Q12C1 (Q12C2's sibling) after it has returned: GnuCOBOL stops with "attempt to CANCEL
      * active program". IBM and the model: START C1 01 C1 02 C1 01 END.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q12.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           CALL 'Q12C2'.
           DISPLAY 'END'.
           STOP RUN.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q12C1 IS COMMON.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 K PIC 99 VALUE 1.
       PROCEDURE DIVISION.
           DISPLAY 'C1 ' K.
           ADD 1 TO K.
           EXIT PROGRAM.
       END PROGRAM Q12C1.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q12C2.
       PROCEDURE DIVISION.
           CALL 'Q12C2N'.
           EXIT PROGRAM.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q12C2N IS COMMON.
       PROCEDURE DIVISION.
           CALL 'Q12C1'.
           CALL 'Q12C1'.
           CANCEL 'Q12C1'.
           CALL 'Q12C1'.
           EXIT PROGRAM.
       END PROGRAM Q12C2N.
       END PROGRAM Q12C2.
       END PROGRAM Q12.
