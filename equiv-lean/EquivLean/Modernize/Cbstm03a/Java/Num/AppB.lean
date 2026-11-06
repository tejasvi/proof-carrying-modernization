import EquivLean.Modernize.Cbstm03a.Java.Num.AppLemmas

/-!
# `app` with the builder's text read from the heap

`appSpecB`: `appSpec` with the old builder text `bText σ d` instead of a quantified `b` in the postcondition
(a postcondition quantifying a value that only a heap fact determines is not instantiated by `jvc` at the call
sites). Used by `para` and `star` (`paraCalleesB`); `app_vcB` proves it like `app_vc`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The text of the builder at `d` (`[]` if there is none). -/
def bText (σ : State) (d : Addr) : JStr :=
  match σ.heap d with
  | some (.builder _ s) => s
  | _ => []

def appSpecB : Spec := Spec.of
  (fun args σ => ∃ (d : Addr) (cap : I32) (sv dv : Value) (b : JStr), args = [.ref d, .int cap, sv, dv] ∧
     σ.heap d = some (.builder "java.lang.StringBuilder" b) ∧ b.length < 2147483648 ∧ 0 ≤ cap.toInt ∧
     StrNN σ sv ∧ StrOk σ dv)
  (fun args σ r σ' => ∀ (d : Addr) (cap : I32) (sv dv : Value), args = [.ref d, .int cap, sv, dv] →
     r = none ∧
       σ'.heap d = some (.builder "java.lang.StringBuilder" (appStr (bText σ d) cap.toInt (argText σ sv) (strOf σ dv))) ∧
       Keeps (fun y => y = d) σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def paraCalleesB : Contracts := [(appSig, appSpecB), (fixSig, fixSpecI)]

theorem toInt_ofNat32b (L : Nat) (h : L < 2147483648) : (BitVec.ofNat 32 L).toInt = L := by
  have := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 L)
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
  split at this <;> omega

theorem take_eq_of_minb {α : Type} (l : List α) (n m : Nat) (h : min n l.length = min m l.length) :
    l.take n = l.take m := by
  apply List.ext_getElem
  · simp only [List.length_take]; exact h
  · intro i h1 h2
    simp only [List.getElem_take]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem app_vcB : MethodVC Gen.prog (fun _ => none) 0 appRef appSpecB [] 60 := by
  jverify [appSpecB, bText, StrNN, StrOk, argText, strOf, Keeps, toInt_ofNat32b, indexOf_bmod, indexOf_emod,
    indexOf_le_eq]
  all_goals (
    simp only [appStr, cutAt]
    split_ifs <;> (try simp only [List.take_take]) <;> first
      | rfl
      | (exfalso; omega)
      | (congr 1; exact (List.take_of_length_le (by omega)).symm)
      | (congr 1; exact take_eq_of_minb _ _ _ (by omega))
      | (congr 1; exact (List.take_of_length_le (by simp only [List.length_take] at *; omega)).symm)
      | (congr 1; exact take_eq_of_minb _ _ _ (by simp only [List.length_take] at *; omega)))

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.app_vcB
