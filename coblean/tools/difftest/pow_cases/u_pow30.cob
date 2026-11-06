       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOW30.
      * A power of more than 30 digits (IBM truncates the intermediate
      * result with a message): the model stops with unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  N99    PIC 99 VALUE 99.
       77  N16    PIC 99 VALUE 16.
       77  W0     PIC S9(5) VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W0 = N99 ** N16
               ON SIZE ERROR DISPLAY 'R01 Z'
           END-COMPUTE.
           DISPLAY 'R02 ' W0.
           STOP RUN.
