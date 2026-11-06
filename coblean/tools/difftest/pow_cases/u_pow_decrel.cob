       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWDR.
      * A relation whose comparands have decimal places (IBM's dmax
      * there is theirs, the resolver's 0): unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  TWO    PIC 9 VALUE 2.
       77  IA     PIC S99 VALUE 4.
       PROCEDURE DIVISION.
           IF IA ** TWO > 1.5 DISPLAY 'R01 Y' ELSE DISPLAY 'R01 N'.
           STOP RUN.
