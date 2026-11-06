       IDENTIFICATION DIVISION.
       PROGRAM-ID. GNEGCMP.
      * GnuCOBOL 3.2 departures found while writing powtest.py (no
      * power involved; the tester avoids both): an unsigned item
      * compared with a negative value, and a negative literal or
      * constant expression compared with an item, behave as if the
      * value were positive (G-ucmpneg, G-negconst); IBM compares
      * algebraically. Every N line differs; the C lines agree.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  IB  PIC 9 VALUE 4.
       01  IA  PIC S99 VALUE -11.
       01  R0  PIC S9(9) VALUE ZERO.
       01  ER0 PIC -(9)9.
       PROCEDURE DIVISION.
           IF IB < -1331 DISPLAY 'N01 Y|' ELSE DISPLAY 'N01 N|'.
           IF IB < (0 - 1331) DISPLAY 'N02 Y|' ELSE DISPLAY 'N02 N|'.
           IF (0 - 1331) < IB DISPLAY 'N03 Y|' ELSE DISPLAY 'N03 N|'.
           IF IB > (1 - 1332) DISPLAY 'N04 Y|' ELSE DISPLAY 'N04 N|'.
           IF (0 - 1331) < IA DISPLAY 'N05 Y|' ELSE DISPLAY 'N05 N|'.
           COMPUTE R0 = (0 - 1331) + IB.
           MOVE R0 TO ER0. DISPLAY 'C01 [' ER0 ']'.
           COMPUTE R0 = IA * (0 - 2).
           MOVE R0 TO ER0. DISPLAY 'C02 [' ER0 ']'.
           STOP RUN.
