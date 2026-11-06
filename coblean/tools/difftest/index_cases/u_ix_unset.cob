      * An index data item read before any SET. IBM gives it no initial
      * value (no VALUE clause is allowed; "If the initial value is not
      * explicitly specified, the value is unpredictable"); GnuCOBOL
      * starts it at 0 and shows 0. The model stops there (invalidData:
      * the item's bytes hold no value until a SET), after the first
      * line.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. IXUNSET.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  TA.
           05  TAE PIC XX OCCURS 6 INDEXED BY IA.
       77  X USAGE INDEX.
       01  N PIC 9(4).
       PROCEDURE DIVISION.
           DISPLAY 'START'
           SET IA TO X
           SET N TO IA
           DISPLAY 'IA ' N
           STOP RUN.
