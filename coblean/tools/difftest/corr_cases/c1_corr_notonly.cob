       IDENTIFICATION DIVISION.
       PROGRAM-ID. P2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05  A        PIC S9(3) VALUE 900.
           05  B        PIC 9(3)V99 VALUE 1.25.
           05  C        PIC 9(2) VALUE 50.
           05  D        PIC X(2) VALUE '12'.
           05  E        PIC 9(2) VALUE 7.
           05  F.
               10 FA    PIC 9 VALUE 3.
       01  G2.
           05  A        PIC S9(3) VALUE 200.
           05  B        PIC 9(3)V9 VALUE 1.
           05  C        PIC 9(2) VALUE 60.
           05  D        PIC 9(2) VALUE 1.
           05  E        PIC ZZ9.
           05  F.
               10 FA    PIC 9 VALUE 4.
       01  G3.
           05  A        PIC S9(3) VALUE 200.
           05  B        PIC 9(3)V9 VALUE 1.
           05  C        PIC 9(2) VALUE 60.
           05  F.
               10 FA    PIC 9 VALUE 4.
       PROCEDURE DIVISION.
       P0.
           MOVE 5 TO E OF G2.
           ADD CORRESPONDING G1 TO G2.
           DISPLAY 'T1 ' G2.
           ADD CORR G1 TO G3 ROUNDED
               ON SIZE ERROR DISPLAY 'T2 SIZE ' G3
               NOT ON SIZE ERROR DISPLAY 'T2 NOSIZE ' G3
           END-ADD.
           DISPLAY 'T2 ' G3.
           SUBTRACT CORR G1 FROM G3
               ON SIZE ERROR DISPLAY 'T3 SIZE ' G3
           END-SUBTRACT.
           DISPLAY 'T3 ' G3.
           MOVE 1 TO A OF G1 C OF G1.
           SUBTRACT CORR G1 FROM G3
               NOT ON SIZE ERROR DISPLAY 'T4 NS ' G3
           END-SUBTRACT.
           DISPLAY 'T4 ' G3.
           MOVE 99 TO C OF G1.
           ADD CORR G1 TO G3
               NOT ON SIZE ERROR DISPLAY 'T5 NS ' G3
           END-ADD.
           DISPLAY 'T5 ' G3.
           STOP RUN.
