       IDENTIFICATION DIVISION.
       PROGRAM-ID. UIR30M.
      * ar2-fix hand case: MULTIPLY ... ROUNDED holds each product as an
      * intermediate result; A16 * L17 can need 33 digits (35 with the
      * places ROUNDED might carry): unsupported (the statement).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A16      PIC 9(16) VALUE 3.
       01  L17      PIC 9(17) VALUE 5.
       01  S2       PIC 99 VALUE 4.
       PROCEDURE DIVISION.
       P0.
           MULTIPLY S2 BY L17 ROUNDED
           DISPLAY "V01 " L17
           MULTIPLY A16 BY L17 ROUNDED
           DISPLAY "U01 " L17
           STOP RUN.
