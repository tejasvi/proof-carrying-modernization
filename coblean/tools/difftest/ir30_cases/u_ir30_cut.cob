       IDENTIFICATION DIVISION.
       PROGRAM-ID. UIR30C.
      * ar2-fix hand case: an integer digit IBM cuts is not 0 (message
      * IGZ0036W, the program goes on): the model stops, unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A16      PIC 9(16) VALUE 2.
       01  BIG16    PIC 9(16) VALUE 9999999999999999.
       01  X17      PIC 9(17) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE X17 = A16 * A16 + 1
           DISPLAY "V01 " X17
      * U01 BIG16 * BIG16 has 32 digits: carried with 30 integer places
           COMPUTE X17 = BIG16 * BIG16 + 1
           DISPLAY "U01 " X17
           STOP RUN.
