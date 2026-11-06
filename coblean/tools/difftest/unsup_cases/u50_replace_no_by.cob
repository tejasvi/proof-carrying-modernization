      * EXPECT-REJECT: REPLACE without BY
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U50.
       REPLACE ==A1== ==B1==.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
