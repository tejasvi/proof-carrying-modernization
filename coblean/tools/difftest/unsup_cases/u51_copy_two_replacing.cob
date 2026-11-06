      * EXPECT-REJECT: a second COPY statement with REPLACING
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U51.
       PROCEDURE DIVISION.
           COPY U51A REPLACING ==X1== BY ==Y1==.
           STOP RUN.
