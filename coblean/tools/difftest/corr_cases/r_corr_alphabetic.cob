       IDENTIFICATION DIVISION.
       PROGRAM-ID. P5.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05  A        OCCURS 2.
               10 AA    PIC X VALUE 'a'.
           05  B        PIC X(2) VALUE 'bb'.
           05  BR REDEFINES B.
               10 BB    PIC X(2).
           05  CC       PIC X(2) VALUE 'cc'.
           05  IX       USAGE INDEX.
           05  PT       USAGE POINTER.
           05  AL       PIC A(2) VALUE 'xy'.
           05  NU       PIC 9(2) VALUE 42.
           05  EDS      PIC ZZ9 VALUE 7.
           05  ALN      PIC X(3) VALUE '123'.
           05  D.
               10 D1    PIC X VALUE 'd'.
           05  E        PIC X VALUE 'e'.
           05  F.
               10 F1    PIC X VALUE 'f'.
       66  RG1 RENAMES B THRU CC.
       01  G2.
           05  A.
               10 AA    PIC X VALUE '-'.
           05  BR.
               10 BB    PIC X(2) VALUE '--'.
           05  B        PIC X(2) VALUE '--'.
           05  CC       PIC X(2) VALUE '--'.
           05  IX       USAGE INDEX.
           05  PT       USAGE POINTER.
           05  AL       PIC 9(2) VALUE 0.
           05  NU       PIC A(2) VALUE '--'.
           05  EDS      PIC 9(3) VALUE 0.
           05  ALN      PIC 9(3) VALUE 0.
           05  D.
               10 D2    PIC X VALUE '-'.
               10 D1    PIC X VALUE '-'.
           05  X.
               10 E     PIC X VALUE '-'.
           05  F        OCCURS 2.
               10 F1    PIC X VALUE '-'.
       01  T1.
           05  TR       OCCURS 3.
               10 TA    PIC X.
               10 TB    PIC 9.
       01  S1.
           05  TA       PIC X VALUE 'q'.
           05  TB       PIC 9 VALUE 7.
       01  H1.
           05  HA       PIC X(4) VALUE 'hhhh'.
       01  H2.
           05  HA.
               10 HB    PIC X(2) VALUE '--'.
               10 HC    OCCURS 2 PIC X VALUE '-'.
       01  W.
           05  WA       PIC X(2) VALUE 'w1'.
           05  WB       PIC 9(2) VALUE 12.
       PROCEDURE DIVISION.
       P0.
           SET IX OF G1 TO 1.
           MOVE CORRESPONDING G1 TO G2.
           DISPLAY 'A=' A OF G2 ' BR=' BR OF G2 ' B=' B OF G2
               ' CC=' CC OF G2.
           DISPLAY 'AL=' AL OF G2 ' NU=' NU OF G2 ' EDS=' EDS OF G2
               ' ALN=' ALN OF G2.
           DISPLAY 'D=' D OF G2 ' X=' X ' F=' F1 OF G2 (1)
               F1 OF G2 (2).
           MOVE SPACES TO T1.
           MOVE CORR S1 TO TR (2).
           DISPLAY 'T1=' T1 '.'.
           MOVE CORR H1 TO H2.
           DISPLAY 'H2=' H2 '.'.
           MOVE CORR W TO W.
           DISPLAY 'W=' W '.'.
           ADD CORR S1 TO TR (2).
           DISPLAY 'T1=' T1 '.'.
           STOP RUN.
