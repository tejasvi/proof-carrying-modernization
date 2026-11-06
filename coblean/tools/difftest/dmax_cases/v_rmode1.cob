       IDENTIFICATION DIVISION.
       PROGRAM-ID. VRMODE1.
      * inr-fix (R2): a COMPUTE whose whole expression is one quotient,
      * into a receiver with a ROUNDED MODE IBM does not have, rounds
      * the exact quotient once, as DIVIDE ... GIVING does (dmax-fix's
      * probe r2probe1.cob). GnuCOBOL -std=ibm agrees in these cases.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 Q    PIC 9.
       77 A    PIC 999 VALUE 251.
       77 B    PIC 999 VALUE 100.
       77 A2   PIC 999 VALUE 201.
       PROCEDURE DIVISION.
      * 251 / 100 = 2.51 rounds to 3; truncated to one place first,
      * 2.5, NEAREST-EVEN would give 2
           DIVIDE A BY B GIVING Q ROUNDED MODE NEAREST-EVEN.
           DISPLAY 'R01 DIVIDE NEAREST-EVEN ' Q.
           COMPUTE Q ROUNDED MODE NEAREST-EVEN = A / B.
           DISPLAY 'R02 COMPUTE NEAREST-EVEN ' Q.
      * plain ROUNDED keeps IBM's intermediate: the same value
           DIVIDE A BY B GIVING Q ROUNDED.
           DISPLAY 'R03 DIVIDE ROUNDED ' Q.
           COMPUTE Q ROUNDED = A / B.
           DISPLAY 'R04 COMPUTE ROUNDED ' Q.
      * 201 / 100 = 2.01 rounds to 3; truncated to one place first,
      * 2.0, AWAY-FROM-ZERO would give 2
           DIVIDE A2 BY B GIVING Q ROUNDED MODE AWAY-FROM-ZERO.
           DISPLAY 'R05 DIVIDE AWAY-FROM-ZERO ' Q.
           COMPUTE Q ROUNDED MODE AWAY-FROM-ZERO = A2 / B.
           DISPLAY 'R06 COMPUTE AWAY-FROM-ZERO ' Q.
      * truncation keeps IBM's intermediate too
           DIVIDE A2 BY B GIVING Q.
           DISPLAY 'R07 DIVIDE TRUNCATION ' Q.
           COMPUTE Q = A2 / B.
           DISPLAY 'R08 COMPUTE TRUNCATION ' Q.
           STOP RUN.
