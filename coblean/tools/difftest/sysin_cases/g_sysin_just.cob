      * G-sysin-just: a JUSTIFIED RIGHT receiver. IBM fills the area from the left with the record
      * ("AB      "); GnuCOBOL right-justifies the line ("      AB").
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GJUST.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 J8 PIC X(8) JUSTIFIED RIGHT.
       PROCEDURE DIVISION.
           ACCEPT J8 FROM SYSIN.
           DISPLAY 'J8 [' J8 ']'.
           STOP RUN.
