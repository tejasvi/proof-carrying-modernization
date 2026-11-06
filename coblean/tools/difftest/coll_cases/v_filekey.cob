      * Indexed file keys keep their binary order under a PROGRAM
      * COLLATING SEQUENCE (IBM RECORD KEY clause: "The collation order
      * of the key is determined by the item's binary value order"):
      * READ NEXT order and START KEY > / >=, while a relation condition
      * on the same values follows the alphabet. Both systems agree.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VFKEY.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       OBJECT-COMPUTER. X
           PROGRAM COLLATING SEQUENCE IS SEQ1.
       SPECIAL-NAMES.
           ALPHABET SEQ1 IS "WVUTSRJIHGFEDCB".
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO "VFKEY.DAT"
              ORGANIZATION INDEXED ACCESS DYNAMIC
              RECORD KEY IS K1 FILE STATUS IS FS.
       DATA DIVISION.
       FILE SECTION.
       FD F1.
       01 R1.
          05 K1 PIC X(2).
          05 V1 PIC X(2).
       WORKING-STORAGE SECTION.
       01 FS PIC XX.
       01 KX PIC X(2).
       PROCEDURE DIVISION.
           OPEN OUTPUT F1.
           MOVE "AA01" TO R1 WRITE R1.
           MOVE "BB02" TO R1 WRITE R1.
           MOVE "CC03" TO R1 WRITE R1.
           MOVE "VV04" TO R1 WRITE R1.
           MOVE "WW05" TO R1 WRITE R1.
           MOVE "ZZ06" TO R1 WRITE R1.
           DISPLAY "W " FS.
           CLOSE F1.
           OPEN INPUT F1.
           PERFORM 6 TIMES
              READ F1 NEXT AT END DISPLAY "EOF"
              NOT AT END DISPLAY "R " R1 END-READ
           END-PERFORM.
           CLOSE F1.
           OPEN INPUT F1.
           MOVE "CC" TO K1
           START F1 KEY > K1 INVALID KEY DISPLAY "INV " FS
              NOT INVALID KEY DISPLAY "STARTED" END-START
           READ F1 NEXT AT END DISPLAY "EOF" NOT AT END DISPLAY "S " R1
           END-READ.
           MOVE "VV" TO K1
           START F1 KEY >= K1 INVALID KEY DISPLAY "INV " FS
              NOT INVALID KEY DISPLAY "STARTED" END-START
           READ F1 NEXT AT END DISPLAY "EOF" NOT AT END DISPLAY "S " R1
           END-READ.
           MOVE "CC" TO KX
           IF K1 > KX DISPLAY "K1 > CC" ELSE DISPLAY "K1 <= CC".
           CLOSE F1.
           STOP RUN.
