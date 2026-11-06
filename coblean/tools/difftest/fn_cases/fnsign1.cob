       IDENTIFICATION DIVISION.
       PROGRAM-ID. FNSIGN1.
      * Signed literals after a separator or an operand in function
      * argument lists, subscripts and operand lists (each COMPUTE is
      * displayed): a sign written directly before digits starts a
      * literal, and a comma or semicolon separates operands.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A PIC S9(4) VALUE 5.
       01  B PIC S9(4) VALUE 7.
       01  I PIC 9(2) VALUE 2.
       01  TT VALUE '0102030405'.
           05 T PIC 99 OCCURS 5.
       01  WS-LINE-COUNTER PIC 9(9) COMP-3 VALUE 40.
       01  WS-PAGE-SIZE PIC 9(3) COMP-3 VALUE 20.
       01  X PIC S9(6)V99 SIGN LEADING SEPARATE.
       PROCEDURE DIVISION.
       P0.
           COMPUTE X = FUNCTION MAX(A, -3)
           DISPLAY 'F01 ' X
           COMPUTE X = FUNCTION MAX(A,-3)
           DISPLAY 'F02 ' X
           COMPUTE X = FUNCTION MAX(A -3)
           DISPLAY 'F03 ' X
           COMPUTE X = FUNCTION MAX(A - 3)
           DISPLAY 'F04 ' X
           COMPUTE X = FUNCTION MAX(1, -3)
           DISPLAY 'F05 ' X
           COMPUTE X = FUNCTION MAX(1 -3)
           DISPLAY 'F06 ' X
           COMPUTE X = FUNCTION MOD(B, -3)
           DISPLAY 'F07 ' X
           COMPUTE X = FUNCTION MAX(A, - 3)
           DISPLAY 'F08 ' X
           COMPUTE X = FUNCTION MAX(A , -3)
           DISPLAY 'F09 ' X
           COMPUTE X = FUNCTION MIN(A, -3, B)
           DISPLAY 'F10 ' X
           COMPUTE X = FUNCTION MAX(A, +3)
           DISPLAY 'F11 ' X
           COMPUTE X = FUNCTION REM(B, -3)
           DISPLAY 'F12 ' X
           COMPUTE X = FUNCTION MAX(-3, A)
           DISPLAY 'F13 ' X
           COMPUTE X = FUNCTION MAX(A; -3)
           DISPLAY 'F14 ' X
           COMPUTE X = FUNCTION MAX(A B)
           DISPLAY 'F15 ' X
           COMPUTE X = FUNCTION MAX((A) -3)
           DISPLAY 'F16 ' X
           COMPUTE X = FUNCTION MAX(A + 1, -3)
           DISPLAY 'F17 ' X
           COMPUTE X = FUNCTION MAX(A + 1 -3)
           DISPLAY 'F18 ' X
           COMPUTE X = A * -3
           DISPLAY 'F19 ' X
           COMPUTE X = A - -3
           DISPLAY 'F20 ' X
           COMPUTE X = A - 3
           DISPLAY 'F21 ' X
           COMPUTE X = FUNCTION MOD(WS-LINE-COUNTER, WS-PAGE-SIZE)
           DISPLAY 'F22 ' X
           COMPUTE X = FUNCTION MIN(-1.5, A)
           DISPLAY 'F23 ' X
           COMPUTE X = FUNCTION ABS(-2.25)
           DISPLAY 'F24 ' X
           COMPUTE X = FUNCTION MAX(A
               , -3)
           DISPLAY 'F25 ' X
           MOVE T(I - 1) TO X
           DISPLAY 'F26 ' X
           MOVE -1025.00 TO X
           DISPLAY 'F27 ' X
           ADD A, -3 TO B
           MOVE B TO X
           DISPLAY 'F28 ' X
           IF FUNCTION MOD(WS-LINE-COUNTER, WS-PAGE-SIZE) = 0
               DISPLAY 'F29 PAGE'
           END-IF
           IF A > -3 DISPLAY 'F30 GT' END-IF
           STOP RUN.
