      * EXPECT-REJECT: LEADING needs one partial word
       IDENTIFICATION DIVISION.
       PROGRAM-ID. U53.
       REPLACE LEADING =='AB'== BY ==X==.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           STOP RUN.
