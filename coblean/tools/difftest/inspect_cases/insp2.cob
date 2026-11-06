      * A1-A4 agree.  B1, G-order (GnuCOBOL deviation): at position 5 of
      * 'BABAX AXBBXA' the first phrase (ALL 'A') does not match and the
      * second (ALL ' A') does, covering position 6: the standard
      * comparison cycle gives 'ByByXbxXBBXy'; GnuCOBOL applies the
      * phrases one after the other over the whole item and gives
      * 'ByByX yXBBXy'.  B2 (phrases swapped) agrees.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. INSP2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  S PIC X(12).
       PROCEDURE DIVISION.
           MOVE '  XBABB BX B' TO S
           INSPECT S REPLACING FIRST ' ' BY ZERO CHARACTERS BY 'y'
           DISPLAY 'A1 ' S
           MOVE '  XBABB BX B' TO S
           INSPECT S REPLACING FIRST ' ' BY '0' CHARACTERS BY 'y'
           DISPLAY 'A2 ' S
           MOVE '  XBABB BX B' TO S
           INSPECT S REPLACING ALL ' ' BY ZERO CHARACTERS BY 'y'
           DISPLAY 'A3 ' S
           MOVE '  XBABB BX B' TO S
           INSPECT S REPLACING FIRST ' ' BY ZERO
           DISPLAY 'A4 ' S
           MOVE 'BABAX AXBBXA' TO S
           INSPECT S REPLACING ALL 'A' BY 'y' ALL ' A' BY 'bx'
           DISPLAY 'B1 ' S
           MOVE 'BABAX AXBBXA' TO S
           INSPECT S REPLACING ALL ' A' BY 'bx' ALL 'A' BY 'y'
           DISPLAY 'B2 ' S
           STOP RUN.
