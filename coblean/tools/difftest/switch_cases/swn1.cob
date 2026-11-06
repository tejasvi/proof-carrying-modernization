      * GnuCOBOL switch names (SWITCH-n, -std=cobol85 as in the NIST
      * suite): the front end accepts them with --profile gnucobol only.
      * Checked by switch_checks.sh.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. SWN1.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           SWITCH-1 IS SW-1 ON STATUS IS ON-SWITCH-1
           SWITCH-36 OFF IS OFF-SWITCH-36.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  W PIC X VALUE 'A'.
       PROCEDURE DIVISION.
       MAIN-PARA.
           IF ON-SWITCH-1 DISPLAY 'S1 ON' ELSE DISPLAY 'S1 OFF' END-IF
           IF OFF-SWITCH-36 DISPLAY 'S36 OFF' ELSE DISPLAY 'S36 ON'
           END-IF
           SET SW-1 TO OFF
           IF ON-SWITCH-1 DISPLAY 'S1 ON' ELSE DISPLAY 'S1 OFF' END-IF
           STOP RUN.
