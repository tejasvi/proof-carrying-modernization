      * SEARCH and SEARCH ALL of an OCCURS DEPENDING ON table cover its current occurrences (the
      * object's value): elements above it are not found, a start index above it ends at once.
      * Expected: GnuCOBOL and the model agree on every line.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VODOS.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 N PIC 99 VALUE 6.
       01 TB.
          05 E OCCURS 1 TO 6 DEPENDING ON N
               ASCENDING KEY IS K INDEXED BY IX.
             10 K PIC X.
       01 J PIC 99.
       PROCEDURE DIVISION.
           MOVE 'ABCDEF' TO TB
           MOVE 4 TO N
           SET IX TO 1
           SEARCH E AT END DISPLAY 'A-END'
              WHEN K(IX) = 'E' DISPLAY 'A-FOUND'
           END-SEARCH
           SET IX TO 1
           SEARCH E AT END DISPLAY 'B-END'
              WHEN K(IX) = 'D' DISPLAY 'B-FOUND'
           END-SEARCH
           SET IX TO 5
           SEARCH E AT END DISPLAY 'C-END'
              WHEN K(IX) = 'E' DISPLAY 'C-FOUND'
           END-SEARCH
           SEARCH ALL E AT END DISPLAY 'D-END'
              WHEN K(IX) = 'E' DISPLAY 'D-FOUND'
           END-SEARCH
           SEARCH ALL E AT END DISPLAY 'E-END'
              WHEN K(IX) = 'C' DISPLAY 'E-FOUND'
           END-SEARCH
           SET J TO IX
           DISPLAY 'F' J
           MOVE 6 TO N
           SEARCH ALL E AT END DISPLAY 'G-END'
              WHEN K(IX) = 'F' DISPLAY 'G-FOUND'
           END-SEARCH
           STOP RUN.
