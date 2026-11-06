       IDENTIFICATION DIVISION.
       PROGRAM-ID. UINR.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  R.
           05  A PIC X(2) VALUE 'aa'.
           05  N PIC 9(2) VALUE 12.
       66  RAN RENAMES A THRU N.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           INITIALIZE RAN.
           DISPLAY 'R=' R.
           STOP RUN.
