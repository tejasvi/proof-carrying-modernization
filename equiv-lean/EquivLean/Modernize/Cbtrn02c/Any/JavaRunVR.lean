import EquivLean.Modernize.Cbtrn02c.JavaSpec

/-!
# CBTRN02C: the reject reason of a daily transaction, as `Model.step` decides it
-/

open EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The reject reason of transaction `t` (0: valid), as `Model.step` decides it. -/
def vreason (xrefs accts : List (List EquivLean.Cobol.Rec.FVal)) (t : List EquivLean.Cobol.Rec.FVal) :
    Int :=
  match Model.findXref xrefs (Model.tCard t) with
  | none => 100
  | some x =>
    match Model.findAcct accts (Model.xAcct x) with
    | none => 101
    | some a =>
      if Cobol.Sem.cmpBytes (Model.aExp a) ((Model.tOrig t).take 10) = .lt then 103
      else if Model.aLimit a < (Cobol.Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt
          (Model.aCC a - Model.aCD a + Model.tAmt t)).2 then 102
      else 0

/-- The description of a reject reason. -/
def descOf (k : Int) : List UInt8 :=
  if k = 100 then CardDemo.Cbtrn02c.badCardDesc
  else if k = 101 then CardDemo.Cbtrn02c.noAcctDesc
  else if k = 102 then CardDemo.Cbtrn02c.overLimitDesc
  else CardDemo.Cbtrn02c.expiredDesc

theorem vreason_cases (xrefs accts : List (List EquivLean.Cobol.Rec.FVal)) (t : List EquivLean.Cobol.Rec.FVal) :
    vreason xrefs accts t = 0 ∨ vreason xrefs accts t = 100 ∨ vreason xrefs accts t = 101 ∨
      vreason xrefs accts t = 102 ∨ vreason xrefs accts t = 103 := by
  unfold vreason
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp

theorem step_reject (xrefs : List (List EquivLean.Cobol.Rec.FVal)) (clk : List UInt8) (s : Model.St) (t : List EquivLean.Cobol.Rec.FVal)
    (h : vreason xrefs s.accts t ≠ 0) :
    Model.step xrefs clk s t = s.reject t (vreason xrefs s.accts t) (descOf (vreason xrefs s.accts t)) := by
  unfold vreason at h ⊢
  unfold Model.step
  split
  · rename_i hx
    simp [hx, descOf]
  · rename_i x hx
    split
    · rename_i ha
      simp [hx, ha, descOf]
    · rename_i a ha
      split
      · rename_i h1
        simp [hx, ha, h1, descOf]
      · rename_i h1
        split
        · rename_i h2
          simp [hx, ha, h1, h2, descOf]
        · rename_i h2
          simp [hx, ha, h1, h2] at h

theorem step_post (xrefs : List (List EquivLean.Cobol.Rec.FVal)) (clk : List UInt8) (s : Model.St) (t : List EquivLean.Cobol.Rec.FVal)
    (h : vreason xrefs s.accts t = 0) :
    ∃ x a, Model.findXref xrefs (Model.tCard t) = some x ∧
      Model.findAcct s.accts (Model.xAcct x) = some a ∧ Model.step xrefs clk s t = s.post clk t x a := by
  unfold vreason at h
  unfold Model.step
  split at h
  · simp at h
  · next x hx =>
    split at h
    · simp at h
    · next a ha =>
      split at h
      · simp at h
      · next h1 =>
        split at h
        · simp at h
        · next h2 =>
          refine ⟨x, a, hx, ha, ?_⟩
          simp only [hx, ha, h1, h2, ↓reduceIte]

end EquivLean.Modernize.Cbtrn02c.Java
