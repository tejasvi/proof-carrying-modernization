       IDENTIFICATION DIVISION.
       PROGRAM-ID. REFNUM.
      * INITIALIZE of reference-modified numeric DISPLAY items: the
      * reference has category alphanumeric and receives SPACE (IBM).
      * GnuCOBOL and the model store the same bytes (the X views).
      * Only GnuCOBOL's DISPLAY of the numeric item itself differs: it
      * shows a space digit as 0 and a space separate sign as + (N1
      * 100056); the model shows the bytes (N1 1   56). inittest.py
      * therefore displays alphanumeric views only.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N1 PIC 9(6) VALUE 123456.
       01  N1X REDEFINES N1 PIC X(6).
       01  N2 PIC S9(6) VALUE -123456.
       01  N2X REDEFINES N2 PIC X(6).
       01  N3 PIC S9(5) SIGN LEADING SEPARATE VALUE -12345.
       01  N3X REDEFINES N3 PIC X(6).
       01  N4 PIC 9(4)V99 VALUE 1234.56.
       01  N4X REDEFINES N4 PIC X(6).
       01  NX PIC 9(6) VALUE 123456.
       01  NXX REDEFINES NX PIC X(6).
       01  G2.
           05  G2A PIC X(4) VALUE 'WXYZ'.
           05  G2B PIC 9(4) VALUE 4321.
       01  I PIC 9 VALUE 2.
       01  L PIC 9 VALUE 3.
       PROCEDURE DIVISION.
           INITIALIZE N1 (2:3)
           DISPLAY 'N1 [' N1X '] [' N1 ']'
           INITIALIZE N2 (1:2)
           DISPLAY 'N2 [' N2X '] [' N2 ']'
           INITIALIZE N3 (1:3)
           DISPLAY 'N3 [' N3X '] [' N3 ']'
           INITIALIZE N4 (I:L)
           DISPLAY 'N4 [' N4X '] [' N4 ']'
           INITIALIZE NX (1:6)
           DISPLAY 'NX [' NXX '] [' NX ']'
           INITIALIZE G2B (2:2)
           DISPLAY 'G2B [' G2 ']'
           STOP RUN.
