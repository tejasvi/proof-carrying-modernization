      * No system input device (cobolrun without --sysin): the model faults at the ACCEPT with
      * unsupported "ACCEPT: no system input device"; GnuCOBOL reads an empty standard input.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. NNODEV.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 PARM-VALUE                      PIC X(8).
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           MOVE 'PRESET01' TO PARM-VALUE.
           ACCEPT PARM-VALUE      FROM SYSIN.
           DISPLAY 'PARM-VALUE [' PARM-VALUE ']'.
           STOP RUN.
