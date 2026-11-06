import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH3

/-!
# CBTRN02C → Java: `db2Timestamp`, `reasonDesc`

`db2Timestamp(clock)`: `YYYY-MM-DD-HH.MM.SS.HH0000` from the first 16 characters of the clock
reading.  `reasonDesc(reason)`: the description of a reject reason.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- What `db2Timestamp(clock)` returns for the clock text `cs`. -/
def db2J (cs : JStr) : JStr :=
  cs.take 4 ++ [45#16] ++ (cs.take 6).drop 4 ++ [45#16] ++ (cs.take 8).drop 6 ++ [45#16] ++
    (cs.take 10).drop 8 ++ [46#16] ++ (cs.take 12).drop 10 ++ [46#16] ++ (cs.take 14).drop 12 ++
    [46#16] ++ (cs.take 16).drop 14 ++ [48#16, 48#16, 48#16, 48#16]

abbrev db2TimestampRef : MethodRef := Gen.Cbtrn02c.«db2Timestamp(java.lang.String)».ref

def db2TimestampSpec : Spec := Spec.of
  (fun args σ => ∃ (c : Addr) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 : JChar), args = [.ref c] ∧
     σ.heap c = some (.str [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20]))
  (fun args σ r σ' => ∀ (c : Addr) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 : JChar), args = [.ref c] →
     σ.heap c = some (.str [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20]) →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (db2J [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20])) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

/-- Statements 12 and 21: the builder holds the timestamp up to the day and up to the minutes. -/
def db2Inv : Invariants :=
  [(12, fun args σ0 fr σ => ∀ (c : Addr) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 : JChar), args = [.ref c] →
    σ0.heap c = some (.str [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20]) →
    ∃ sb, fr.get 0 = some (.ref sb) ∧ fr.get 1 = some (.ref c) ∧
      σ.heap sb = some (.builder "java.lang.StringBuilder" [c0, c1, c2, c3, 45#16, c4, c5, 45#16, c6, c7, 45#16]) ∧
      σ.heap c = some (.str [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20]) ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
      σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c"),
   (21, fun args σ0 fr σ => ∀ (c : Addr) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 : JChar), args = [.ref c] →
    σ0.heap c = some (.str [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20]) →
    ∃ sb, fr.get 0 = some (.ref sb) ∧ fr.get 1 = some (.ref c) ∧
      σ.heap sb = some (.builder "java.lang.StringBuilder" [c0, c1, c2, c3, 45#16, c4, c5, 45#16, c6, c7, 45#16, c8, c9, 46#16, c10, c11, 46#16, c12, c13, 46#16]) ∧
      σ.heap c = some (.str [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20]) ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
      σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem db2Timestamp_vc :
    MethodVC Gen.prog (fun _ => none) 0 db2TimestampRef db2TimestampSpec db2Inv 60 := by
  jverify [db2TimestampSpec, db2Inv, Grows, db2J, valueOfArg_char, jstrLitT, Native.valueOfArg, JType.isRef,
    valueOfObj_eq, valueOfObjN_ref]

end EquivLean.Modernize.Cbtrn02c.Java
