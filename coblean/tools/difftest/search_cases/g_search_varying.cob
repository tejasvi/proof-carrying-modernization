      * G-searchvary (GnuCOBOL deviation): SEARCH ... VARYING an integer
      * item.  IBM: "whenever the index-name for identifier-1 is
      * incremented, identifier-2 is simultaneously incremented by 1":
      * CNT 0, found at IX 3 after two increments: CNT 2.  GnuCOBOL sets
      * CNT to the occurrence number: 3.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. SRCH2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  TAB.
           05  ENT OCCURS 5 INDEXED BY IX.
               10  K PIC X(2).
               10  V PIC 9(3).
       01  CNT PIC 9(3).
       PROCEDURE DIVISION.
           MOVE 'AA001BB002CC003BB004DD005' TO TAB
           SET IX TO 1
           MOVE 0 TO CNT
           SEARCH ENT VARYING CNT AT END DISPLAY 'S4 END ' CNT
             WHEN V(IX) > 3 DISPLAY 'S4 GT3 ' V(IX) ' ' CNT
             WHEN K(IX) = 'CC' DISPLAY 'S4 CC ' CNT
           END-SEARCH
           STOP RUN.
