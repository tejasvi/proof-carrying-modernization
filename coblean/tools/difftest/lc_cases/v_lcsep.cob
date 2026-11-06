       IDENTIFICATION DIVISION.
       PROGRAM-ID. VLCSEP.
      * Commas that stay separators after PIC (a comma followed by a
      * space or by the end of the line), commas the fix does not touch,
      * and PICTURE strings that begin with a comma whose output agrees
      * with GnuCOBOL (zero in an all-Z, BLANK WHEN ZERO or all-* item:
      * the whole item spaces or asterisks). lctest.py --run.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  S01 PIC , ZZ9.
       01  S02 PIC ,
               ZZ9.
       01  S03 PICTURE IS , 999.
       01  S04 PIC ZZ,ZZ9.
       01  S05 PIC 9(3), VALUE 7.
       01  S06 PIC X(4), VALUE 'AB'.
       01  Z01 PIC ,ZZZ.
       01  Z02 PIC ,ZZ9 BLANK WHEN ZERO.
       01  Z03 PIC ,***.
       01  Z04 PICTURE IS ,**.**.
       01  Z05 PIC ,$$$.
       PROCEDURE DIVISION.
       P0.
           MOVE 5 TO S01 DISPLAY 'Q01 5 [' S01 ']'
           MOVE 5 TO S02 DISPLAY 'Q02 5 [' S02 ']'
           MOVE 5 TO S03 DISPLAY 'Q03 5 [' S03 ']'
           MOVE 12345 TO S04 DISPLAY 'Q04 12345 [' S04 ']'
           DISPLAY 'Q05 [' S05 ']'
           DISPLAY 'Q06 [' S06 ']'
           MOVE 0 TO Z01 DISPLAY 'Q07 0 [' Z01 ']'
           MOVE ZERO TO Z02 DISPLAY 'Q08 ZERO [' Z02 ']'
           MOVE 0 TO Z03 DISPLAY 'Q09 0 [' Z03 ']'
           MOVE 0 TO Z04 DISPLAY 'Q10 0 [' Z04 ']'
           MOVE 0 TO Z05 DISPLAY 'Q11 0 [' Z05 ']'
           STOP RUN.
