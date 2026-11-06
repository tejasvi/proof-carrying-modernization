       IDENTIFICATION DIVISION.
       PROGRAM-ID. IVALZERO.
      * VALUE ZERO in PIC ZZ9.99 holds '000000': no value edits to it.
      * IBM leaves its unedited value undefined: the model stops
      * (invalidData); GnuCOBOL moves 0.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  E1 PIC ZZ9.99 VALUE ZERO.
       01  N1 PIC S9(4)V99.
       01  N1X REDEFINES N1 PIC X(6).
       PROCEDURE DIVISION.
       P0.
           DISPLAY 'E1[' E1 ']'
           MOVE E1 TO N1
           DISPLAY 'N1[' N1X ']'
           STOP RUN.
