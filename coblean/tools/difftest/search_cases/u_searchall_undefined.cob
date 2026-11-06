      * SEARCH ALL where IBM's result is not defined; the model reports
      * them as unsupported (fault) instead of choosing:
      * U1: the table is out of KEY order (IBM: "the results of SEARCH
      *     ALL are unpredictable");
      * U2: several elements satisfy the WHEN condition (IBM: the one
      *     found is any of them).
      * GnuCOBOL prints its binary search's choice for U1.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. SRCHA2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  TAB.
           05  ENT OCCURS 4 ASCENDING KEY IS K INDEXED BY IX.
               10  K PIC X(2).
       PROCEDURE DIVISION.
           MOVE 'AACCBBDD' TO TAB
           SEARCH ALL ENT AT END DISPLAY 'U1 END'
             WHEN K(IX) = 'BB' DISPLAY 'U1 BB'
           END-SEARCH
           MOVE 'AABBBBDD' TO TAB
           SEARCH ALL ENT AT END DISPLAY 'U2 END'
             WHEN K(IX) = 'BB' DISPLAY 'U2 BB'
           END-SEARCH
           STOP RUN.
