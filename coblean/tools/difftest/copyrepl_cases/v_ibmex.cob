      * After the COPY examples of IBM Enterprise COBOL 6.4 (Language
      * Reference, Comparison and replacement examples 2 3 5 6 7 8):
      * pseudo-text without blanks inside the delimiters (G-ptblank,
      * G-pwblank), no OCCURS DEPENDING ON, unsigned items. Examples 7
      * and 8 disagree on :TAG:-GROSS-PAY under ==:TAG:== and TRAILING
      * ==GROSS-PAY==; by the text-word rules (colons are separators,
      * -GROSS-PAY is a text word of its own) it is PAY7-NET-PAY, as in
      * Example 8.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VIBMEX.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       COPY CRPAY2 REPLACING A BY PAYROLL B BY PAY-CODE C BY GROSS-PAY
                             D BY HOURS.
       COPY CRPAY3 REPLACING ==:TAG:== BY ==Pay3==.
       COPY CRPAY5 REPLACING LEADING ==DEPT== BY ==PAY5==.
       COPY CRPAY6 REPLACING TRAILING ==GROSS-PAY== BY ==NET-PAY==.
       COPY CRPAY7 REPLACING ==:TAG:== BY ==PAY7==
                             TRAILING ==GROSS-PAY== BY ==NET-PAY==.
       PROCEDURE DIVISION.
           MOVE 40 TO HOURS (2) PAY3-HOURS (3).
           DISPLAY 'E2 ' PAY-CODE '|' GROSS-PAY '|' HOURS (2) '|'.
           DISPLAY 'E3 ' PAY3-WEEK '|' PAY3-GROSS-PAY '|'
               PAY3-HOURS (3) '|'.
           DISPLAY 'E5 ' PAY5 '|' PAY5-WEEK '|' PAY5-GROSS-PAY '|'.
           DISPLAY 'E6 ' PAY6-WEEK '|' PAY6-NET-PAY '|'.
           DISPLAY 'E7 ' PAY7-WEEK '|' PAY7-NET-PAY '|'.
           DISPLAY 'E8 ' PAY78-NET-PAY '|' PAY8 '|'.
           STOP RUN.
