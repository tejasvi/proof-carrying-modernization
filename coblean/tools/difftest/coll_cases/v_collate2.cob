      * NC219A's alphabet "F" "U" "N" ALSO HIGH-VALUE ALSO LOW-VALUE
      * "Y", plus THROUGH descending, ALSO and a 2-character literal.
      * LOW-VALUE is "F", HIGH-VALUE X"FE" (the highest character not
      * given) in VALUE, MOVE, DISPLAY, comparisons and level 88;
      * level-88 THRU and EVALUATE THRU follow the sequence. Both
      * systems agree on every line.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VCOLL2.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       OBJECT-COMPUTER. X
           PROGRAM COLLATING SEQUENCE IS SEQ1.
       SPECIAL-NAMES.
           ALPHABET SEQ1 IS "F" "U" "N" ALSO HIGH-VALUE ALSO LOW-VALUE
              "Y" "c" THRU "a" "0" ALSO "9" "QR".
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 H PIC X VALUE HIGH-VALUE.
       01 L PIC X VALUE LOW-VALUE.
       01 A3 PIC X(3).
       01 B3 PIC X(3).
       01 C1 PIC X.
       01 C2 PIC X.
       01 Z3 PIC 999 VALUE 199.
       01 D4 PIC X(4).
          88 D-RNG VALUE "AAAA" THRU "ZZZZ".
          88 D-HI VALUE HIGH-VALUE.
          88 D-LO VALUE LOW-VALUE.
       01 FF PIC X VALUE X"FF".
       01 ZZ PIC X VALUE X"00".
       PROCEDURE DIVISION.
           DISPLAY "H=" H "|L=" L "|".
           MOVE HIGH-VALUE TO A3 MOVE LOW-VALUES TO B3
           DISPLAY "A3=" A3 "|B3=" B3 "|".
           DISPLAY "HV=" HIGH-VALUE "|LV=" LOW-VALUE "|".
           MOVE "F" TO C1 MOVE "U" TO C2
           IF C1 < C2 DISPLAY "C01 Y" ELSE DISPLAY "C01 N".
           MOVE "N" TO C1
           IF C2 < C1 DISPLAY "C02 Y" ELSE DISPLAY "C02 N".
           IF C1 = FF DISPLAY "C03 Y" ELSE DISPLAY "C03 N".
           IF C1 = ZZ DISPLAY "C04 Y" ELSE DISPLAY "C04 N".
           IF FF = ZZ DISPLAY "C05 Y" ELSE DISPLAY "C05 N".
           IF C1 = HIGH-VALUE DISPLAY "C06 Y" ELSE DISPLAY "C06 N".
           MOVE "Y" TO C2
           IF C2 > FF DISPLAY "C07 Y" ELSE DISPLAY "C07 N".
           MOVE "c" TO C1 MOVE "b" TO C2
           IF C1 < C2 DISPLAY "C08 Y" ELSE DISPLAY "C08 N".
           MOVE "0" TO C1 MOVE "9" TO C2
           IF C1 = C2 DISPLAY "C09 Y" ELSE DISPLAY "C09 N".
           IF C1 = "9" DISPLAY "C10 Y" ELSE DISPLAY "C10 N".
           MOVE "A" TO C1 MOVE "Y" TO C2
           IF C1 > C2 DISPLAY "C11 Y" ELSE DISPLAY "C11 N".
           MOVE "F" TO A3 MOVE "FU" TO B3
           IF A3 > B3 DISPLAY "C12 Y" ELSE DISPLAY "C12 N".
           IF Z3 = "100" DISPLAY "C13 Y" ELSE DISPLAY "C13 N".
           MOVE "R" TO C1 MOVE "A" TO C2
           IF C1 < C2 DISPLAY "C14 Y" ELSE DISPLAY "C14 N".
           MOVE X"FE" TO C1 MOVE "z" TO C2
           IF C1 > C2 DISPLAY "C15 Y" ELSE DISPLAY "C15 N".
           IF H = HIGH-VALUE DISPLAY "C16 Y" ELSE DISPLAY "C16 N".
           IF L = "F" DISPLAY "C17 Y" ELSE DISPLAY "C17 N".
           MOVE "FFFF" TO D4
           IF D-RNG DISPLAY "C18 Y" ELSE DISPLAY "C18 N".
           MOVE "BBBB" TO D4
           IF D-RNG DISPLAY "C19 Y" ELSE DISPLAY "C19 N".
           MOVE HIGH-VALUE TO D4
           IF D-HI DISPLAY "C20 Y" ELSE DISPLAY "C20 N".
           MOVE "FFFF" TO D4
           IF D-LO DISPLAY "C21 Y" ELSE DISPLAY "C21 N".
           EVALUATE D4
              WHEN "AAAA" THRU "ZZZZ" DISPLAY "E1 RNG"
              WHEN OTHER DISPLAY "E1 OTH"
           END-EVALUATE.
           EVALUATE D4
              WHEN "FFFA" THRU "FFFU" DISPLAY "E2 RNG"
              WHEN "FFFF" DISPLAY "E2 EQ"
              WHEN OTHER DISPLAY "E2 OTH"
           END-EVALUATE.
           MOVE FUNCTION MIN("A" D4 "Y") TO A3 DISPLAY "M1 " A3 "|".
           MOVE FUNCTION MAX("N" FF ZZ) TO C1 DISPLAY "M2 " C1 "|".
           STOP RUN.
