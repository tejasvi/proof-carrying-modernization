      * SEARCH ALL on tables in KEY order with unique keys (where IBM's
      * result is defined): found, not found, two keys with AND, a
      * descending numeric key, a key compared with an item.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. SRCHA1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  TAB.
           05  ENT OCCURS 6 ASCENDING KEY IS K1 K2 INDEXED BY IX.
               10  K1 PIC X(2).
               10  K2 PIC 9(2).
               10  V PIC X(3).
       01  TD.
           05  DEN OCCURS 5 DESCENDING KEY IS DK INDEXED BY JX.
               10  DK PIC 9(3).
               10  DV PIC X(2).
       01  W PIC X(2).
       PROCEDURE DIVISION.
           MOVE 'AA01ONEAA03TWOAB02THRBA01FOUBA05FIVCC00SIX' TO TAB
           MOVE '090AA040BB030CC015DD007EE' TO TD
           SEARCH ALL ENT AT END DISPLAY 'A1 END'
             WHEN K1(IX) = 'AB' AND K2(IX) = 2 DISPLAY 'A1 ' V(IX)
           END-SEARCH
           SEARCH ALL ENT AT END DISPLAY 'A2 END'
             WHEN K1(IX) = 'AB' AND K2(IX) = 3 DISPLAY 'A2 ' V(IX)
           END-SEARCH
           MOVE 'BA' TO W
           SEARCH ALL ENT AT END DISPLAY 'A3 END'
             WHEN K1(IX) = W AND K2(IX) = 5 DISPLAY 'A3 ' V(IX)
           END-SEARCH
           SEARCH ALL ENT AT END DISPLAY 'A4 END'
             WHEN K1(IX) = 'CC' AND K2(IX) = 0 DISPLAY 'A4 ' V(IX)
           END-SEARCH
           SEARCH ALL DEN AT END DISPLAY 'D1 END'
             WHEN DK(JX) = 40 DISPLAY 'D1 ' DV(JX)
           END-SEARCH
           SEARCH ALL DEN AT END DISPLAY 'D2 END'
             WHEN DK(JX) = 15 DISPLAY 'D2 ' DV(JX)
           END-SEARCH
           SEARCH ALL DEN AT END DISPLAY 'D3 END'
             WHEN DK(JX) = 50 DISPLAY 'D3 ' DV(JX)
           END-SEARCH
           STOP RUN.
