      * LENGTH OF / FUNCTION LENGTH of a group containing an OCCURS DEPENDING ON table: its length
      * varies with the object (GnuCOBOL: the current length), and the front end computes LENGTH OF as
      * a constant: the statement is unsupported.
      * Expected: GnuCOBOL shows "A 005"; the model stops at that DISPLAY with unsupported "LENGTH OF ...".
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UODOLEN.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 N PIC 99 VALUE 3.
       01 G.
          05 H PIC XX VALUE 'AB'.
          05 T OCCURS 1 TO 5 DEPENDING ON N PIC X.
       01 L PIC 999.
       PROCEDURE DIVISION.
           MOVE LENGTH OF G TO L
           DISPLAY 'A ' L
           STOP RUN.
