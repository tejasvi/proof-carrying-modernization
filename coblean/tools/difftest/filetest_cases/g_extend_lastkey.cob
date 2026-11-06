      * G-extend and G-lastkey (GnuCOBOL), ACCESS SEQUENTIAL, OPEN EXTEND:
      * E1: K02 into a file holding K01, K03.  IBM 21 (the first record must
      *     be above the highest key in the file); model 21; GnuCOBOL 00 and
      *     K02 is inserted (E-reads show K01 K02 K03).
      * L1: K08 with alternate key A1 in use: both 22.  L2: K05: model 00
      *     (above the highest record written, K03); GnuCOBOL 21 because the
      *     failed K08 became its previous key (G-lastkey).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. REXTEND.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT KF ASSIGN TO 'rextend.dat'
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS K-KEY
               ALTERNATE RECORD KEY IS K-ALT
               FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD  KF.
       01  K-REC.
           05  K-KEY   PIC X(3).
           05  K-ALT   PIC X(2).
           05  K-DATA  PIC X(3).
       WORKING-STORAGE SECTION.
       01  FS PIC XX.
       PROCEDURE DIVISION.
           OPEN OUTPUT KF
           MOVE 'K01A1D01' TO K-REC
           WRITE K-REC
           MOVE 'K03A3D03' TO K-REC
           WRITE K-REC
           CLOSE KF
           OPEN EXTEND KF
           MOVE 'K02A2D02' TO K-REC
           WRITE K-REC
           DISPLAY 'E1 K02 ' FS
           CLOSE KF
           OPEN INPUT KF
           READ KF
           DISPLAY 'E2 ' FS ' ' K-REC
           READ KF
           DISPLAY 'E3 ' FS ' ' K-REC
           READ KF
           DISPLAY 'E4 ' FS ' ' K-REC
           CLOSE KF
           OPEN OUTPUT KF
           MOVE 'K01A1D01' TO K-REC
           WRITE K-REC
           MOVE 'K03A3D03' TO K-REC
           WRITE K-REC
           CLOSE KF
           OPEN EXTEND KF
           MOVE 'K08A1D08' TO K-REC
           WRITE K-REC
           DISPLAY 'L1 K08-ALT-A1 ' FS
           MOVE 'K05A5D05' TO K-REC
           WRITE K-REC
           DISPLAY 'L2 K05 ' FS
           CLOSE KF
           STOP RUN.
