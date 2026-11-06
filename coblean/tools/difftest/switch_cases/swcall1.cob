      * A caller and a callee (swsub1.cob) that both use UPSI-0: link.py
      * refuses to link them (each would have its own copy of the switch).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. SWCALL1.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           UPSI-0 IS U0 ON STATUS IS U0-ON.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  W PIC X VALUE 'A'.
       PROCEDURE DIVISION.
       MAIN-PARA.
           CALL 'SWSUB1'
           IF U0-ON DISPLAY 'ON' ELSE DISPLAY 'OFF' END-IF
           STOP RUN.
