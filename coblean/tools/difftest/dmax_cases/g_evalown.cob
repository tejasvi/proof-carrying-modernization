       IDENTIFICATION DIVISION.
       PROGRAM-ID. GEVALOWN.
      * G-evalown: IBM evaluates an EVALUATE subject or object "without
      * regard to the attributes of its comparand" (PG, Arithmetic
      * expressions in nonarithmetic statements); GnuCOBOL gives it the
      * dmax of the relation with each object. Model: IBM.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 A    PIC 9(3) VALUE 5.
       77 C    PIC 9(3) VALUE 3.
       77 D1   PIC 9V9 VALUE 1.6.
       PROCEDURE DIVISION.
      * subject on its own: dmax 0, 5 / 3 = 1 (GnuCOBOL 1.6: W1)
           EVALUATE A / C
             WHEN 1.6 DISPLAY 'V01 W1|'
             WHEN 1 DISPLAY 'V01 W2|'
             WHEN OTHER DISPLAY 'V01 O|'
           END-EVALUATE.
      * an item object with 1 place: the subject is still 1
           EVALUATE A / C
             WHEN D1 DISPLAY 'V02 W1|'
             WHEN OTHER DISPLAY 'V02 O|'
           END-EVALUATE.
      * the object with the division, on its own: 1, not D1's 1.6
           EVALUATE D1
             WHEN A / C DISPLAY 'V03 W1|'
             WHEN OTHER DISPLAY 'V03 O|'
           END-EVALUATE.
      * THRU: 1 is outside 1.6 THRU 1.7
           EVALUATE A / C
             WHEN 1.6 THRU 1.7 DISPLAY 'V04 W1|'
             WHEN OTHER DISPLAY 'V04 O|'
           END-EVALUATE.
           STOP RUN.
