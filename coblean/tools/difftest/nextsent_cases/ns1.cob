      * NEXT SENTENCE inside an inline PERFORM leaves the loop: control
      * passes to the statement after the next separator period, which
      * follows END-PERFORM (the shape of CBTRN03C's date check).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. NS1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  I PIC 9(2) VALUE 0.
       01  T PIC 9(2) VALUE 0.
       PROCEDURE DIVISION.
       MAIN-PARA.
           DISPLAY 'START'.
           PERFORM UNTIL I >= 5
             ADD 1 TO I
             IF I = 3
                NEXT SENTENCE
             ELSE
                CONTINUE
             END-IF
             ADD 1 TO T
             DISPLAY 'ITER ' I ' ' T
           END-PERFORM.
           DISPLAY 'AFTER ' I ' ' T.
           PERFORM UNTIL I >= 9
             ADD 1 TO I
             IF I = 7
                NEXT SENTENCE
             END-IF
             DISPLAY 'LOOP2 ' I
           END-PERFORM
           DISPLAY 'SAME SENTENCE ' I.
           DISPLAY 'END ' I.
           STOP RUN.
