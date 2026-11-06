      * G-odoinit: INITIALIZE of a group containing an OCCURS DEPENDING ON table. IBM: "you cannot use
      * the INITIALIZE statement to initialize a variably-located item or a variable-length item";
      * GnuCOBOL 3.2 initializes the header and the current occurrences (N = 2).
      * Expected: GnuCOBOL shows "A[   0 0c3d4e5]"; the model stops at the INITIALIZE with
      * unsupported "INITIALIZE ... of a group containing an OCCURS DEPENDING ON table".
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GODOINI.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 N PIC 99 VALUE 5.
       01 G.
          05 H PIC XX VALUE 'AB'.
          05 T OCCURS 1 TO 5 DEPENDING ON N.
             10 TX PIC X.
             10 TN PIC 9.
       PROCEDURE DIVISION.
           MOVE 'a1' TO T(1) MOVE 'b2' TO T(2) MOVE 'c3' TO T(3)
           MOVE 'd4' TO T(4) MOVE 'e5' TO T(5)
           MOVE 2 TO N
           INITIALIZE G
           MOVE 5 TO N
           DISPLAY 'A[' G ']'
           STOP RUN.
