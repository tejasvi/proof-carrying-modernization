      * G-sepcomma: pseudo-text-1 that is a separator comma (IBM: it
      * matches separator commas as a text word; cobc 3.2 never does).
      * Expected: L01 and L03 differ (model A B, E F; GnuCOBOL AB, EF).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GSEPCOMMA.
       PROCEDURE DIVISION.
           COPY CRCOMMA REPLACING ==,== BY ==SPACE==.
           STOP RUN.
