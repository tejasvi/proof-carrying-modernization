      * COBSWAIT's statements on a card whose first 8 characters are not all digits: the MOVE
      * faults with invalidData in the model (GnuCOBOL moves 0).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. ICOBSW.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 MVSWAIT-TIME                    PIC 9(8) COMP.
       01 PARM-VALUE                      PIC X(8).
       01 MTD                             PIC 9(8).
       PROCEDURE DIVISION.
           ACCEPT PARM-VALUE      FROM SYSIN.
           DISPLAY 'PARM-VALUE [' PARM-VALUE ']'.
           MOVE  PARM-VALUE       TO MVSWAIT-TIME.
           MOVE MVSWAIT-TIME TO MTD.
           DISPLAY 'MVSWAIT-TIME [' MTD ']'.
           STOP RUN.
