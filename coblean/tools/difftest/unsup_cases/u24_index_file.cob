      * EXPECT-FAULT: index data item FX in a file record
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U24.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F ASSIGN TO 'U24DAT'.
       DATA DIVISION.
       FILE SECTION.
       FD  F.
       01  FR.
           05  FA PIC X(4).
           05  FX USAGE INDEX.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
