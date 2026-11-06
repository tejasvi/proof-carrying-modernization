      * Index data items are not INITIALIZE receivers (IBM rule 1a: not
      * MOVE receivers). Needs index-fix's USAGE INDEX (the 0518Z front
      * end rejects it). Expected model output: GI UNCHANGED, GN 11.
      * GnuCOBOL 3.2 -std=ibm sets GI to 11 (index-fix's G-initindex), so
      * this case is checked against the expected lines, not GnuCOBOL.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. IRX1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  T.
           05 TE OCCURS 5 INDEXED BY TX PIC X.
       01  G.
           05 GN PIC 9(2).
           05 GI USAGE INDEX.
       PROCEDURE DIVISION.
       MAIN-PARA.
           SET TX TO 3
           SET GI TO TX
           INITIALIZE G REPLACING NUMERIC BY 11
           SET TX TO 1
           SET TX TO GI
           IF TX = 3 DISPLAY 'GI UNCHANGED' ELSE DISPLAY 'GI CHANGED'
           END-IF
           DISPLAY 'GN ' GN
           STOP RUN.
