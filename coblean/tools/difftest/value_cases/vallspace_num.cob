      * VALUE ALL SPACE on a numeric item is not valid (IBM: the VALUE
      * literal of a numeric item must be numeric, and only ZERO may stand
      * for a numeric literal): GnuCOBOL -std=ibm and the front end both
      * reject it ("invalid VALUE clause" / "nonnumeric VALUE for a
      * numeric item").
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VALLS1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  N8 PIC 9(3) VALUE ALL SPACES.
       PROCEDURE DIVISION.
       MAIN-PARA.
           DISPLAY N8
           STOP RUN.
