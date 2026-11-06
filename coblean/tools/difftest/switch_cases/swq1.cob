      * IBM-only switch forms (GnuCOBOL rejects the first): a condition
      * name qualified by its switch's mnemonic name (IBM: "the associated
      * mnemonic-name ... is considered the conditional variable and can be
      * used for qualification"), and SET of a switch-status condition name
      * TO TRUE (an unsupported statement). Checked by switch_checks.sh.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. SWQ1.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       SPECIAL-NAMES.
           UPSI-0 IS U0 ON STATUS IS U0-ON OFF STATUS IS U0-OFF.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  W PIC X VALUE 'A'.
       PROCEDURE DIVISION.
       MAIN-PARA.
           IF U0-ON OF U0 DISPLAY 'Q ON' ELSE DISPLAY 'Q OFF' END-IF
           SET U0-ON TO TRUE
           STOP RUN.
