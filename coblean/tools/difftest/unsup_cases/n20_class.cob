      * EXPECT-RUN
      * (u02's program: a CLASS clause is modelled now)
       IDENTIFICATION DIVISION.
       PROGRAM-ID. N20.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           CLASS HEXDIG IS '0' THRU '9' 'A' THRU 'F'.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
