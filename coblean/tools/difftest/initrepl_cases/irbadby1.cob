      * INITIALIZE ... REPLACING BY a group item: IBM requires an
      * elementary sending item, the front end rejects the program.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. IRB1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G.
           05 GA PIC X(3).
       01  H.
           05 HA PIC X(4).
       PROCEDURE DIVISION.
       MAIN-PARA.
           INITIALIZE G REPLACING ALPHANUMERIC BY H
           STOP RUN.
