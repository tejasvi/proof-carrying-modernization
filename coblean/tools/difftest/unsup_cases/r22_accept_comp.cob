      * EXPECT-REJECT: ACCEPT N: not a group or an item of usage DISPLAY
       IDENTIFICATION DIVISION.
       PROGRAM-ID. R12.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N PIC 9(8) COMP.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           ACCEPT N FROM SYSIN.
           STOP RUN.
