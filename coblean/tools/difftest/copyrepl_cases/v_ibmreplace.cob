      * The REPLACE example of IBM Enterprise COBOL 6.4 (Language
      * Reference, REPLACE statement), as written there. IBM documents
      * the output "Original: (Hello, Mom!)" and "Modified: Hello,
      * COBOL!". cobc 3.2 aborts on LEADING ==XX-== BY ====.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. REPLEXMP.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       REPLACE =="(Hello, World!)"== BY =="(Hello, Mom!)"==.
       01 WS-STRING1 PIC X(30) VALUE "(Hello, World!)".
       01 WS-STRING2 PIC X(30) VALUE "Hello, COBOL!".
       PROCEDURE DIVISION.
           DISPLAY "Original: " WS-STRING1
       REPLACE LEADING ==XX-== BY ====
               ==:TAG:== BY ==STRING==
               TRAILING ==1== BY ==2==.
           DISPLAY "Modified: " XX-WS-:TAG:1
       REPLACE OFF.
           GOBACK.
