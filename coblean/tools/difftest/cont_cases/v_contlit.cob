      * Literals continued over 3 and 4 lines whose middle lines end
      * before column 72 (IBM: the spaces through column 72 of every
      * continued line belong to the literal), one whose middle line
      * reaches column 72, a comparison with a 3-line literal (as NIST
      * SM201A COPY-TEST-11), a 4-line DISPLAY literal and a 3-line
      * literal in a copybook (as the CCVS-C-1 header of NIST K6SCA).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VCONTLIT.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 L3 PIC X(130) VALUE "AB
      -    "CD
      -    "EF".
       01 L4 PIC X(200) VALUE "GH
      -    "IJ
      -    "KL
      -    "MN".
       01 LF PIC X(130) VALUE "OPQRSTUVWXYZOPQRSTUVWXYZOPQRSTUVWXYZOPQRS
      -    "XYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZXYZ
      -    "END".
       01 T120 PIC X(120) VALUE SPACES.
       COPY CTLIT.
       PROCEDURE DIVISION.
           DISPLAY "L3 " L3 "|".
           DISPLAY "L4 " L4 "|".
           DISPLAY "LF " LF "|".
           DISPLAY "LC " LC "|".
           MOVE "Z" TO T120 (120:1).
           IF T120 = "
      -    "
      -    "         Z"
               DISPLAY "C3 EQ"
           ELSE
               DISPLAY "C3 NE".
           DISPLAY "M4 " "P
      -    "Q
      -    "R
      -    "S" "|".
           STOP RUN.
