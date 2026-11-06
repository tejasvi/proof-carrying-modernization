       IDENTIFICATION DIVISION.
       PROGRAM-ID. REFCOMP.
      * INITIALIZE of a reference-modified COMP-3 or COMP item: not IBM
      * COBOL (data-name-1 of a reference modification must have usage
      * DISPLAY). The model stops at the first one as unsupported;
      * GnuCOBOL stores spaces into the packed and binary bytes.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  NC3 PIC 9(5) COMP-3 VALUE 12345.
       01  NB PIC 9(4) COMP VALUE 1234.
       PROCEDURE DIVISION.
           INITIALIZE NC3 (1:2)
           DISPLAY 'NC3 [' NC3 ']'
           INITIALIZE NB (1:1)
           DISPLAY 'NB [' NB ']'
           STOP RUN.
