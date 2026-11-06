      * G-sysin-num: a numeric receiver. IBM transfers the characters ("12AB  "); GnuCOBOL moves the
      * line as an alphanumeric sender (000012).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GNUM.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 N6 PIC 9(6).
       PROCEDURE DIVISION.
           MOVE ZERO TO N6.
           ACCEPT N6 FROM SYSIN.
           DISPLAY 'N6 [' N6 ']'.
           STOP RUN.
