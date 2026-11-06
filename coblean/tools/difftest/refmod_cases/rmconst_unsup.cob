      * Reference modifiers the front end does not evaluate stay
      * unsupported statements (each faults when reached): a division,
      * a name times a literal, two names, a negated name, a scaled
      * literal. Check: cobolfe.py lists five unsupported statements.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. RMCU1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  T1 PIC X(10) VALUE 'ABCDEFGHIJ'.
       01  I PIC 99 VALUE 2.
       01  J PIC 99 VALUE 3.
       PROCEDURE DIVISION.
       MAIN-PARA.
           DISPLAY T1 (6 / 2:)
           DISPLAY T1 (2 * I:)
           DISPLAY T1 (I + J:)
           DISPLAY T1 (- I + 4:)
           DISPLAY T1 (1.0:)
           STOP RUN.
