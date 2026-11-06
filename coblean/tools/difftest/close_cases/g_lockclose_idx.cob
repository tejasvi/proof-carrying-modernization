      * G-lockclose, indexed file: a CLOSE of a file closed WITH LOCK.
      * IBM: 42 (the file is not in an open mode; Language Reference
      * 6.4, CLOSE statement, Table 34). GnuCOBOL 3.2 ends with a
      * segmentation fault at the second CLOSE ('attempt to reference
      * invalid memory address'): status gnucobol-abend; the model ends
      * normally with M02 42. closetest.py does not generate this case.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GLOCKCLX.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F3 ASSIGN TO "glockclx-f3.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS RANDOM
               RECORD KEY IS K3
               FILE STATUS IS ST3.
       DATA DIVISION.
       FILE SECTION.
       FD F3.
       01 R3.
          05 K3 PIC X(3).
          05 V3 PIC X(5).
       WORKING-STORAGE SECTION.
       01 ST3 PIC XX VALUE "..".
       PROCEDURE DIVISION.
       M0.
           OPEN OUTPUT F3
           CLOSE F3 WITH LOCK
           DISPLAY "M01 LOCK " ST3 "|"
           CLOSE F3
           DISPLAY "M02 CLOSE AGAIN " ST3 "|"
           STOP RUN.
