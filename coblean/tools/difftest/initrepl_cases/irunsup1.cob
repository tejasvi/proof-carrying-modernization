      * INITIALIZE forms that stay named unsupported statements (checked
      * by initrepl_checks.sh: one unsupported line per statement, in
      * order) and one the front end rejects (irbadby1.cob).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. IRU1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G.
           05 GA PIC X(3).
           05 GN PIC 9(3).
           05 GT OCCURS 3 PIC X(2).
       01  I PIC 9 VALUE 2.
       01  H.
           05 HA PIC X(4).
       01  P POINTER.
       PROCEDURE DIVISION.
       MAIN-PARA.
           INITIALIZE G WITH FILLER
           INITIALIZE G ALL TO VALUE
           INITIALIZE G NUMERIC TO VALUE
           INITIALIZE G THEN TO DEFAULT
           INITIALIZE G REPLACING NUMERIC BY 1 THEN TO DEFAULT
           INITIALIZE GA (2:1) REPLACING ALPHANUMERIC BY 'Z'
           INITIALIZE GT (I) REPLACING ALPHANUMERIC BY 'Z'
           INITIALIZE H REPLACING ALPHANUMERIC BY GT (I)
           INITIALIZE H REPLACING ALPHANUMERIC BY GA (1:2)
           INITIALIZE G REPLACING ALPHANUMERIC BY GA
           INITIALIZE P REPLACING NUMERIC BY 0
           INITIALIZE G H REPLACING NUMERIC BY 7
           STOP RUN.
