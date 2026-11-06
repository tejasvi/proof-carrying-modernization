      * After the REPLACE example of IBM Enterprise COBOL 6.4 (Language
      * Reference, REPLACE statement), with LEADING ==XX-== BY ==WS-==
      * in place of BY ==== (cobc 3.2 aborts on an empty partial word).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VREPLACE.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       REPLACE =="(Hello, World!)"== BY =="(Hello, Mom!)"==.
       01 WS-STRING1 PIC X(30) VALUE "(Hello, World!)".
       01 WS-STRING2 PIC X(30) VALUE "Hello, COBOL!".
       PROCEDURE DIVISION.
           DISPLAY "Original: " WS-STRING1
       REPLACE LEADING ==XX-== BY ==WS-==
               ==:TAG:== BY ==STRING==
               TRAILING ==1== BY ==2==.
           DISPLAY "Modified: " XX-:TAG:1
       REPLACE OFF.
           DISPLAY "Off: " WS-STRING1 '|'.
           COPY CRREPL1 OF 'libalt'.
           STOP RUN.
