      * G-sysin-eof: the input has ended. IBM leaves the receiving area unchanged (PRESET01,
      * 777777); GnuCOBOL moves a space (spaces, 000000).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GEOF.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 A8 PIC X(8).
       01 N6 PIC 9(6).
       PROCEDURE DIVISION.
           MOVE 'PRESET01' TO A8.
           ACCEPT A8 FROM SYSIN.
           DISPLAY 'A8 [' A8 ']'.
           MOVE 777777 TO N6.
           ACCEPT N6 FROM SYSIN.
           DISPLAY 'N6 [' N6 ']'.
           STOP RUN.
