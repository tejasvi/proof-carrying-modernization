      * EXPECT-REJECT: library names are not supported
       IDENTIFICATION DIVISION.
       PROGRAM-ID. R01.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       COPY CPYA OF MYLIB.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
