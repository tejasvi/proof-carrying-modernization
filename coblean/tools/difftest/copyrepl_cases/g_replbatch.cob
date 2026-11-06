      * G-replbatch: a REPLACE statement is in effect up to the next
      * one or the end of its separately compiled program (IBM), so it
      * ends with the END PROGRAM of a batch program and stays in
      * effect in the programs that program contains; cobc 3.2 keeps it
      * in effect into the next program of the source. Expected: L02
      * L03 L04 differ (model 1 4 1, GnuCOBOL 2 5 3); L01 agrees.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GREPLB1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 C1 PIC 9 VALUE 0.
       PROCEDURE DIVISION.
           REPLACE ==ADD 1 TO== BY ==ADD 2 TO==.
           ADD 1 TO C1.
           DISPLAY 'L01 ' C1.
           CALL 'GREPLB2'.
           CALL 'GREPLB3'.
           STOP RUN.
       END PROGRAM GREPLB1.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GREPLB2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 C2 GLOBAL PIC 9 VALUE 0.
       PROCEDURE DIVISION.
           ADD 1 TO C2.
           DISPLAY 'L02 ' C2.
           REPLACE ==ADD 1 TO== BY ==ADD 3 TO==.
           CALL 'GREPLB2N'.
           GOBACK.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GREPLB2N.
       PROCEDURE DIVISION.
           ADD 1 TO C2.
           DISPLAY 'L03 ' C2.
           GOBACK.
       END PROGRAM GREPLB2N.
       END PROGRAM GREPLB2.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GREPLB3.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 C3 PIC 9 VALUE 0.
       PROCEDURE DIVISION.
           ADD 1 TO C3.
           DISPLAY 'L04 ' C3.
           GOBACK.
       END PROGRAM GREPLB3.
