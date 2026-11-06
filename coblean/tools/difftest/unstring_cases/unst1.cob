       IDENTIFICATION DIVISION.
       PROGRAM-ID. UNST1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  S PIC X(20).
       01  A PIC X(5).
       01  B PIC X(5).
       01  C PIC X(5).
       01  DA PIC X(2).
       01  DB PIC X(2).
       01  CA PIC 9(2).
       01  CB PIC 9(2).
       01  P PIC 9(2).
       01  T PIC 9(2).
       01  N PIC 9(4).
       PROCEDURE DIVISION.
           MOVE 'AB,CDE,,FGHIJKL,M  ' TO S
           MOVE ALL '*' TO A B C
           UNSTRING S DELIMITED BY ',' INTO A B C
           DISPLAY 'U1 ' A '|' B '|' C
           MOVE ALL '*' TO A B C
           UNSTRING S DELIMITED BY ALL ',' INTO A B C
           DISPLAY 'U2 ' A '|' B '|' C
           MOVE ALL '*' TO A B C
           MOVE 0 TO CA CB T
           MOVE '**' TO DA DB
           UNSTRING S DELIMITED BY ',' OR 'K' INTO A DELIMITER IN DA
               COUNT IN CA B DELIMITER IN DB COUNT IN CB
               TALLYING IN T
           DISPLAY 'U3 ' A '|' DA '|' CA '|' B '|' DB '|' CB '|' T
           MOVE ALL '*' TO A B C
           MOVE 4 TO P
           MOVE 0 TO T
           UNSTRING S DELIMITED BY ',' INTO A B WITH POINTER P
               TALLYING IN T
               ON OVERFLOW DISPLAY 'U4 OVF'
               NOT ON OVERFLOW DISPLAY 'U4 NOOVF'
           END-UNSTRING
           DISPLAY 'U4 ' A '|' B '|' P '|' T
           MOVE ALL '*' TO A B C
           MOVE 30 TO P
           UNSTRING S DELIMITED BY ',' INTO A WITH POINTER P
               ON OVERFLOW DISPLAY 'U5 OVF'
           END-UNSTRING
           DISPLAY 'U5 ' A '|' P
           MOVE ALL '*' TO A B C
           MOVE 1 TO P
           UNSTRING S INTO A B C WITH POINTER P
           DISPLAY 'U6 ' A '|' B '|' C '|' P
           MOVE 'XY 0123 Z' TO S
           MOVE ALL '*' TO A
           MOVE 0 TO N
           UNSTRING S DELIMITED BY ALL SPACE INTO A N
           DISPLAY 'U7 ' A '|' N
           MOVE 'ONE TWO' TO S
           MOVE ALL '*' TO A B C
           UNSTRING S DELIMITED BY ' ' INTO A B C
           DISPLAY 'U8 ' A '|' B '|' C
           STOP RUN.
