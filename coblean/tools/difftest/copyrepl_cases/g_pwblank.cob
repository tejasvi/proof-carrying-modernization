      * G-pwblank: blanks inside partial-word delimiters, as IBM's own
      * examples write them (LEADING == DEPT == BY == PAYROLL ==); cobc
      * 3.2 rejects them (syntax error, expecting ==). Expected:
      * GnuCOBOL cobc-error, model L01 x1, L02 y1, L03 z1.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GPWBLANK.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 PAY-X PIC X(2) VALUE 'x1'.
       01 Y-PAY PIC X(2) VALUE 'y1'.
       01 QB-Z PIC X(2) VALUE 'z1'.
       PROCEDURE DIVISION.
           COPY CRBLANK REPLACING ==:TAG:== BY ==PAY==
                                  LEADING == QA == BY == QB ==.
           STOP RUN.
