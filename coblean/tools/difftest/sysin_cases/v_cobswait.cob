      * COBSWAIT's statements (CardDemo app/cbl/COBSWAIT.cbl) with the CALL replaced by DISPLAYs, on
      * the card of app/jcl/WAITSTEP.jcl (fixed-length 80-byte records): GnuCOBOL = model.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VCOBSW.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 MVSWAIT-TIME                    PIC 9(8) COMP.
       01 PARM-VALUE                      PIC X(8).
       01 MTD                             PIC 9(8).
       PROCEDURE DIVISION.
           ACCEPT PARM-VALUE      FROM SYSIN.
           MOVE  PARM-VALUE       TO MVSWAIT-TIME.
           MOVE MVSWAIT-TIME TO MTD.
           DISPLAY 'PARM-VALUE [' PARM-VALUE '] MVSWAIT-TIME [' MTD ']'.
           STOP RUN.
