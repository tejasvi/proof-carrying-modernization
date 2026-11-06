      * CLOSE ... REEL of an indexed file. IBM: "The REEL, UNIT, and NO
      * REWIND phrases are not valid for VSAM files" (Language Reference
      * 6.4, CLOSE statement, format 1, note 1): the front end reports
      * the CLOSE as unsupported. (GnuCOBOL 3.2 closes the file, 00.)
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UCLREELX.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F3 ASSIGN TO "uclreelx-f3.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC
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
           DISPLAY "I01 " ST3 "|"
           CLOSE F3 REEL
           DISPLAY "I02 REEL " ST3 "|"
           STOP RUN.
