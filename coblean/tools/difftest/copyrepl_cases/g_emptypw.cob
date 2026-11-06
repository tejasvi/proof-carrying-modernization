      * An empty partial-word-2 deletes the matched characters (IBM);
      * cobc 3.2 aborts ("unknown (signal)", "Please report this!").
      * Expected: GnuCOBOL cobc-error, model L01 v1, L02 v2.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GEMPTYPW.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 A PIC X(2) VALUE 'v1'.
       01 B-ZZ PIC X(2) VALUE 'v2'.
       PROCEDURE DIVISION.
           COPY CREMPTY REPLACING LEADING ==ZZ-== BY ====
                                  TRAILING ==-YY== BY ====.
           STOP RUN.
