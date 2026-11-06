      * Serial SEARCH: found, search from a later index, not found (AT
      * END), two WHENs (the first true one wins), start past the table,
      * VARYING an index of the same table (it becomes the search
      * index), no AT END.  VARYING an integer item: g_search_varying.cob.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. SRCH1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  TAB.
           05  ENT OCCURS 5 INDEXED BY IX JX.
               10  K PIC X(2).
               10  V PIC 9(3).
       01  CNT PIC 9(3).
       PROCEDURE DIVISION.
           MOVE 'AA001BB002CC003BB004DD005' TO TAB
           SET IX TO 1
           SEARCH ENT AT END DISPLAY 'S1 END'
             WHEN K(IX) = 'BB' DISPLAY 'S1 BB ' V(IX)
           END-SEARCH
           SET IX TO 3
           SEARCH ENT AT END DISPLAY 'S2 END'
             WHEN K(IX) = 'BB' DISPLAY 'S2 BB ' V(IX)
           END-SEARCH
           SET IX TO 1
           SEARCH ENT AT END DISPLAY 'S3 END'
             WHEN K(IX) = 'ZZ' DISPLAY 'S3 ZZ'
           END-SEARCH
           SET IX TO 1
           SEARCH ENT AT END DISPLAY 'S4 END'
             WHEN V(IX) > 3 DISPLAY 'S4 GT3 ' V(IX)
             WHEN K(IX) = 'CC' DISPLAY 'S4 CC ' V(IX)
           END-SEARCH
           SET IX TO 6
           SEARCH ENT AT END DISPLAY 'S5 END'
             WHEN K(IX) = 'AA' DISPLAY 'S5 AA'
           END-SEARCH
           SET JX TO 2
           SEARCH ENT VARYING JX AT END DISPLAY 'S6 END'
             WHEN K(JX) = 'DD' DISPLAY 'S6 DD ' V(JX)
           END-SEARCH
           SET IX TO 1
           SEARCH ENT
             WHEN K(IX) = 'CC' DISPLAY 'S7 CC'
           END-SEARCH
           SET IX TO 1
           SEARCH ENT
             WHEN K(IX) = 'QQ' DISPLAY 'S8 QQ'
           END-SEARCH
           DISPLAY 'S8 AFTER'
           STOP RUN.
