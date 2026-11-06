      * G-sysin-edit: edited receivers. IBM transfers the characters ("1.5   ", "ABCDE"); GnuCOBOL
      * edits them ("  1.50", "AB CD").
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GEDIT.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 E1 PIC ZZ9.99.
       01 AE1 PIC XXBXX.
       PROCEDURE DIVISION.
           ACCEPT E1 FROM SYSIN.
           DISPLAY 'E1 [' E1 ']'.
           ACCEPT AE1 FROM SYSIN.
           DISPLAY 'AE1 [' AE1 ']'.
           STOP RUN.
