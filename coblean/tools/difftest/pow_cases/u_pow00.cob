       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOW00.
      * Zero raised to the power zero (IBM: a size error, or 1 with a
      * message): the model stops with unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  NZ     PIC 9 VALUE 0.
       77  W0     PIC S9(5) VALUE 0.
       PROCEDURE DIVISION.
           COMPUTE W0 = NZ ** NZ.
           DISPLAY 'R01 ' W0.
           STOP RUN.
