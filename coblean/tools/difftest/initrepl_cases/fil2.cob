      * G-fillersep: GnuCOBOL 3.2 initializes FILLER items with SIGN
      * SEPARATE (lines 1-3 and 5); IBM's INITIALIZE rule 1a excludes
      * every FILLER item without WITH FILLER, as the model does.
      * Run: filetest.py --run fil2.cob (lines 1, 2, 3, 5 differ).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. FIL2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G.
           05 G1A PIC S9(4) COMP.
           05 FILLER PIC S9(3) SIGN LEADING SEPARATE.
           05 G1C PIC A(1).
       01  GX REDEFINES G.
           05 GXA PIC XX.
           05 GXB PIC X(4).
           05 GXC PIC X.
       01  H.
           05 HA PIC X(2).
           05 FILLER PIC S9(3) SIGN LEADING SEPARATE.
       01  K.
           05 FILLER PIC S9(3) SIGN LEADING SEPARATE.
           05 KA PIC 9(2).
       01  M.
           05 FILLER PIC 9(3).
           05 MA PIC 9(2).
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE ALL '#' TO G
           INITIALIZE G REPLACING NUMERIC BY -17
           DISPLAY '1 [' GXB ']'
           MOVE ALL '#' TO H
           INITIALIZE H REPLACING NUMERIC BY -17
           DISPLAY '2 [' H ']'
           MOVE ALL '#' TO K
           INITIALIZE K REPLACING NUMERIC BY -17
           DISPLAY '3 [' K ']'
           MOVE ALL '#' TO M
           INITIALIZE M REPLACING NUMERIC BY 17
           DISPLAY '4 [' M ']'
           MOVE ALL '#' TO K
           INITIALIZE K
           DISPLAY '5 [' K ']'
           STOP RUN.
