      * G-sysin-long: a receiving area longer than the record. IBM reads the next record to fill
      * it ("SHORT", 75 spaces, "NEXT", 16 spaces with 80-byte records); GnuCOBOL pads one line.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GLONG.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 A100 PIC X(100).
       PROCEDURE DIVISION.
           MOVE ALL '*' TO A100.
           ACCEPT A100.
           DISPLAY 'A100 [' A100 ']'.
           STOP RUN.
