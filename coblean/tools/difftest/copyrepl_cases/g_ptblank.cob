      * G-ptblank: blanks at the ends of pseudo-text-2 add no spaces
      * (IBM: spaces only where the text already has them; Example 7
      * writes == PAYROLL == and gets PAYROLL-GROSS-PAY); cobc 3.2 keeps
      * them (PAY -X, Y- PAY: rejected). Expected: GnuCOBOL cobc-error,
      * model L01 x1, L02 y1, L03 z1.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GPTBLANK.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 PAY-X PIC X(2) VALUE 'x1'.
       01 Y-PAY PIC X(2) VALUE 'y1'.
       01 QB-Z PIC X(2) VALUE 'z1'.
       PROCEDURE DIVISION.
           COPY CRBLANK REPLACING ==:TAG:== BY == PAY ==
                                  ==QA-Z== BY ==QB-Z==.
           STOP RUN.
