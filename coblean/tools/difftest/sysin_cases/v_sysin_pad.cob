      * Variable-length records: a record shorter than the area, then the end of the input. IBM:
      * "If EOF is encountered after data has been moved and before the receiving area has been
      * filled, the receiving area is padded with spaces": "AB   ", as GnuCOBOL.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VPAD.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 A5 PIC X(5).
       PROCEDURE DIVISION.
           MOVE ALL '*' TO A5.
           ACCEPT A5 FROM SYSIN.
           DISPLAY 'A5 [' A5 ']'.
           STOP RUN.
