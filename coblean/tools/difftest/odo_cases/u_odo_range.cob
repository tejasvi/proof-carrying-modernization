      * An object outside integer-1 .. integer-2 when its table or a group containing it is referenced:
      * IBM: "The behavior is undefined if the value of the object is outside of the range integer-1
      * through integer-2" -> the model faults with range. GnuCOBOL -std=ibm uses the value as it is
      * (here 7 occurrences of a 5-occurrence table); with -std=cobol85 --debug it stops only at an
      * element reference ("OCCURS DEPENDING ON 'N' out of bounds").
      * Expected: both show A; the model then stops (fault range), GnuCOBOL goes on.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UODORNG.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 N PIC 99 VALUE 5.
       01 G.
          05 H PIC XX VALUE 'AB'.
          05 T OCCURS 1 TO 5 DEPENDING ON N PIC X.
       01 W PIC X(12).
       PROCEDURE DIVISION.
           MOVE '12345' TO G
           DISPLAY 'A[' G ']'
           MOVE 7 TO N
           MOVE G TO W
           DISPLAY 'B[' W ']'
           STOP RUN.
