      * Variable-length records: one empty record, then the end of the input. IBM: "If EOF is
      * encountered before any data has been moved to the receiving area, padding will not take
      * place and the contents of the receiving area are unchanged": no byte was moved, the area
      * keeps *****. GnuCOBOL: an empty line gives spaces.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GEMPTY.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 B5 PIC X(5).
       PROCEDURE DIVISION.
           MOVE ALL '*' TO B5.
           ACCEPT B5 FROM SYSIN.
           DISPLAY 'B5 [' B5 ']'.
           STOP RUN.
