import Cobol
open Cobol

def fA : FieldDesc := { off := 0, len := 3, kind := .num { digits := 5, scale := 2, signed := true, usage := .packed } }
def fB : FieldDesc := { off := 3, len := 5, kind := .num { digits := 5, scale := 0, signed := true } }
def fX : FieldDesc := { off := 8, len := 4, kind := .alnum }
def rA : DataRef := { desc := fA }
def rB : DataRef := { desc := fB }
def rX : DataRef := { desc := fX }

def P : Program := {
  memSize := 12
  paras := #[
    { name := "MAIN", body := [[.perform 0 1 (.para 2), .display [.ref rB, .ref rX], .stop .run]] },
    { name := "P1", body := [[.move (.num (-12345) 2) [rA], .move (.alnum [0xC1, 0xC2]) [rX], .goTo 2]] },
    { name := "P1B", body := [[.move (.num 999 0) [rB]]] },
    { name := "P2", body := [[.arith (.giving (.mul (.ref rA) (.lit 15 1))) [⟨rB, .nearestAwayFromZero⟩] false [] []]] }
  ]
}

def showRes (r : Sem.Res) : String :=
  s!"{repr r.1} mem={r.2.mem.bytes.toList.map (fun b => b.toNat)} out={repr r.2.out}"

#eval showRes (P.run {} 100 (P.initState (Mem.fill 12 0)))

-- kernel evaluation of a concrete run
example : (P.run {} 100 (P.initState (Mem.fill 12 0))).1 = .stop .run := by decide
