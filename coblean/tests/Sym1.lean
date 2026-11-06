import Cobol
open Cobol

def fmtA : NumFmt := { digits := 5, scale := 2, signed := true, usage := .packed }
def fmtB : NumFmt := { digits := 5, scale := 0, signed := true }

def P : Program := {
  memSize := 8
  paras := #[
    { name := "MAIN", body := [[
        .arith (.giving (.mul (.ref { desc := { off := 0, len := 3, kind := .num fmtA } }) (.lit 15 1)))
          [⟨{ desc := { off := 3, len := 5, kind := .num fmtB } }, .nearestAwayFromZero⟩] false [] [],
        .stop .run]] }
  ]
}

example (m : Mem) (hm : m.size = 8) (a : Int) (ha : decodeNum {} fmtA (m.read 0 3) = some a) :
    let r := P.run {} 10 (P.initState m)
    r.1 = .stop .run ∧ decodeNum {} fmtB (r.2.mem.read 3 5) = some (Sem.fitNum {} fmtB (divRound .nearestAwayFromZero (a * 15) 1000)).2 := by
  simp only [fmtA] at ha
  cobol_sym [P, ha, hm, fmtA, fmtB]
