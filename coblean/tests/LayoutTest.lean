import Cobol
open Cobol
-- 01 WS-ACCT.
--    05 WS-ID      PIC X(6).
--    05 WS-BAL     PIC S9(7)V99 COMP-3.        5 bytes
--    05 WS-BAL-X REDEFINES WS-BAL PIC X(5).
--    05 WS-HIST OCCURS 3.
--       10 WS-AMT  PIC S9(5)V99.                7 bytes
--       10 WS-CODE PIC X.                       1 byte
--    05 WS-CNT     PIC S9(4) COMP.              2 bytes
-- 01 WS-FLAG PIC X VALUE 'N'.
def recs : List Item := [
  { id := 1, level := 1, name := "WS-ACCT", children := [
    { id := 2, level := 5, name := "WS-ID", pic := some (.alnum 6), value := some (.fig .space) },
    { id := 3, level := 5, name := "WS-BAL", pic := some (.num 9 2 true), usage := .packed, value := some (.num 12345 2) },
    { id := 4, level := 5, name := "WS-BAL-X", pic := some (.alnum 5), redefines := some 3 },
    { id := 5, level := 5, name := "WS-HIST", occurs := 3, children := [
      { id := 6, level := 10, name := "WS-AMT", pic := some (.num 7 2 true) },
      { id := 7, level := 10, name := "WS-CODE", pic := some (.alnum 1), value := some (.alnum [0xC1]) } ] },
    { id := 8, level := 5, name := "WS-CNT", pic := some (.num 4 0 true), usage := .binary } ] },
  { id := 9, level := 1, name := "WS-FLAG", pic := some (.alnum 1), value := some (.alnum [0xD5]) } ]
def L := layout Config.ibm recs
#eval L.size
#eval L.items.map (fun p => (p.id, p.name, p.desc.off, p.desc.len, p.dims))
#eval (L.inits Config.ibm).map (fun p => (p.1, p.2.map (·.toNat)))
