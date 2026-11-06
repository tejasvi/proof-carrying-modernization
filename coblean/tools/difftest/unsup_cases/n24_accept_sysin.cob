      * EXPECT-RUN
       IDENTIFICATION DIVISION.
       PROGRAM-ID. N16.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           SYSIPT IS CARDS.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A PIC X(8).
       01  N PIC 9(4) VALUE 0.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           IF N = 1
               ACCEPT A
               ACCEPT A FROM SYSIN
               ACCEPT N FROM CARDS
           END-IF.
           STOP RUN.
