      * G-dline: the text words of a debugging line take part in
      * matching, then the line is a comment (IBM, no WITH DEBUGGING
      * MODE); cobc 3.2 without -fdebugging-line drops the line before
      * matching (NIST SM206A PST-TEST-009, which the NIST reference
      * compiles with -fdebugging-line). Expected: L01 and L02 differ
      * (model H1 and PASS, GnuCOBOL F1 and FAIL*); L03 agrees.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GDLINE.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 P-OR-F PIC X(5) VALUE SPACE.
       PROCEDURE DIVISION.
           COPY CRDLINE REPLACING =='F1' 'F2'== BY =='H1'==
                ==FAIL. THIS IS GARBAGE. DISPLAY== BY ==PASS. DISPLAY==.
           DISPLAY 'L02 ' P-OR-F.
           STOP RUN.
       PASS.
           MOVE 'PASS ' TO P-OR-F.
       FAIL.
           MOVE 'FAIL*' TO P-OR-F.
