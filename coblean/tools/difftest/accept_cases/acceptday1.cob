      * ACCEPT FROM DAY (YYDDD), DAY YYYYDDD and DAY-OF-WEEK (1 is
      * Monday) into numeric and alphanumeric items, checked against
      * DATE YYYYMMDD of the same run with INTEGER-OF-DATE (C lines, Y =
      * it holds); the V line shows the values. acceptday_check.sh
      * (tools/difftest) runs it with GnuCOBOL (its clock) and with the
      * model at fixed clock readings; date(1) checks its V lines.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. ACCDAY1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 D8 PIC 9(8).
       01 DY PIC 9(5).
       01 DY7 PIC 9(7).
       01 DW PIC 9.
       01 DX PIC X(5).
       01 DWX PIC X.
       01 Y4 PIC 9(4).
       01 E7 PIC 9(7).
       01 E5 PIC 9(5).
       01 EW PIC 9.
       PROCEDURE DIVISION.
           ACCEPT D8 FROM DATE YYYYMMDD
           ACCEPT DY FROM DAY
           ACCEPT DY7 FROM DAY YYYYDDD
           ACCEPT DW FROM DAY-OF-WEEK
           ACCEPT DX FROM DAY
           ACCEPT DWX FROM DAY-OF-WEEK
           COMPUTE Y4 = D8 / 10000
           COMPUTE E7 = Y4 * 1000 + FUNCTION INTEGER-OF-DATE(D8)
              - FUNCTION INTEGER-OF-DATE(Y4 * 10000 + 101) + 1
           COMPUTE E5 = FUNCTION MOD(E7, 100000)
           COMPUTE EW =
              FUNCTION MOD(FUNCTION INTEGER-OF-DATE(D8) - 1, 7)
              + 1
           IF DY = E5 DISPLAY 'C1 Y' ELSE DISPLAY 'C1 N'.
           IF DY7 = E7 DISPLAY 'C2 Y' ELSE DISPLAY 'C2 N'.
           IF DW = EW DISPLAY 'C3 Y' ELSE DISPLAY 'C3 N'.
           IF DX = DY DISPLAY 'C4 Y' ELSE DISPLAY 'C4 N'.
           IF DWX = DW DISPLAY 'C5 Y' ELSE DISPLAY 'C5 N'.
           DISPLAY 'V ' DY ' ' DY7 ' ' DW ' ' DX '|' DWX '|'.
           STOP RUN.
