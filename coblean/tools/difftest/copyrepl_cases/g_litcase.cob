      * G-litcase: literals compare character for character (IBM);
      * cobc 3.2 matches 'abc' by the operand 'ABC'. Expected: L02
      * differs (model abc, GnuCOBOL Q); L01, L03 agree.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GLITCASE.
       PROCEDURE DIVISION.
           COPY CRLIT REPLACING 'ABC' BY 'Q'.
           STOP RUN.
