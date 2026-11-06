      * DISPLAY of a signed numeric literal: IBM gives no form for its
      * sign; the front end makes the statement unsupported ("DISPLAY of
      * a signed numeric literal"). GnuCOBOL 3.2 writes "-15".
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UDISPLM.
       PROCEDURE DIVISION.
       P0.
           DISPLAY 'D01 [' -1.5 ']'
           STOP RUN.
