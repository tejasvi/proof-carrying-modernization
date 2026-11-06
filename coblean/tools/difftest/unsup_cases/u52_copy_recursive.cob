      * EXPECT-REJECT: a nested COPY cannot cause recursion
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U52.
       PROCEDURE DIVISION.
           COPY U52A REPLACING ==X1== BY ==Y1==.
           STOP RUN.
