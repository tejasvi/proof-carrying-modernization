       IDENTIFICATION DIVISION.
       PROGRAM-ID. REFMOD.
      * INITIALIZE of reference-modified identifiers: IBM makes the
      * reference an elementary alphanumeric item, which receives
      * SPACE; the bytes outside it stay. Before 2026-10-27 the
      * resolver initialized the whole item (A1 8 spaces, G1 4 spaces
      * and 0000). filetest.py --run: GnuCOBOL and the model agree.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A1 PIC X(8) VALUE 'ABCDEFGH'.
       01  A2 PIC X(8) VALUE 'ABCDEFGH'.
       01  G1.
           05  G1A PIC X(4) VALUE 'WXYZ'.
           05  G1B PIC 9(4) VALUE 4321.
       01  NG.
           05  NGA PIC 9(3) VALUE 123.
           05  NGB PIC 9(3) VALUE 456.
       01  E1 PIC ZZ9.99 VALUE 12.34.
       01  B1 PIC AAAA VALUE 'ABCD'.
       01  AE1 PIC XX0XX VALUE 'AB0CD'.
       01  TB.
           05  T1 OCCURS 3 PIC X(5) VALUE 'QRSTU'.
       01  I PIC 9 VALUE 2.
       01  L PIC 9 VALUE 3.
       PROCEDURE DIVISION.
           INITIALIZE A1 (3:4)
           DISPLAY 'A1 [' A1 ']'
           INITIALIZE A2 (5:)
           DISPLAY 'A2 [' A2 ']'
           INITIALIZE G1 (3:4)
           DISPLAY 'G1 [' G1 ']'
           INITIALIZE NG (2:3)
           DISPLAY 'NG [' NG ']'
           INITIALIZE E1 (1:3)
           DISPLAY 'E1 [' E1 ']'
           INITIALIZE B1 (2:2)
           DISPLAY 'B1 [' B1 ']'
           INITIALIZE AE1 (2:3)
           DISPLAY 'AE1 [' AE1 ']'
           INITIALIZE T1 (2) (I:L)
           DISPLAY 'T1 [' TB ']'
           STOP RUN.
