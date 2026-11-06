      * INITIALIZE ... REPLACING of an index data item (the identifier
      * itself) is a named unsupported statement with its own message;
      * an index name and a condition name keep theirs (checked by
      * initrepl_checks.sh, X1 to X3).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. IRX2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  T.
           05 TE OCCURS 5 INDEXED BY TX PIC X.
       01  G.
           05 GN PIC 9(2).
              88 GN-ONE VALUE 1.
           05 GI USAGE INDEX.
       PROCEDURE DIVISION.
       MAIN-PARA.
           SET TX TO 3
           SET GI TO TX
           INITIALIZE GI REPLACING NUMERIC BY 11
           INITIALIZE TX REPLACING NUMERIC BY 11
           INITIALIZE GN-ONE REPLACING NUMERIC BY 11
           DISPLAY 'END'
           STOP RUN.
