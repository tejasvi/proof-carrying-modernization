import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM4s

/-!
# CBTRN02C → Java: `writeTransaction` as a function of the state at the call
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

abbrev ltKey : FieldKey := ("Cbtrn02c$Result", "transactFileWrites")
abbrev trIdKey : FieldKey := ("Cbtrn02c$TranRecord", "tranId")

theorem fld_of {σ : State} {a : Addr} {c : ClassName} {fs : List (FieldKey × Value)} {k : FieldKey}
    {v : Value} (h : σ.heap a = some (.plain c fs)) (hk : Fields.get fs k = some v) : fld σ a k = v := by
  simp [fld, fieldsOf, h, hk]

def writeTransactionSpecF : Spec := Spec.of
  writeTransactionSpec.pre
  (fun args σ r' σ' => ∀ (r wT lK : Addr), args = [.ref r, .ref wT, .ref lK] →
     r' = some (.int 0) ∧
     ∃ (y : Addr) (fsy : List (FieldKey × Value)) (mK' mT' : Nat),
       σ'.heap lK = some (.list .arrayList (listOf σ lK ++ [fld σ wT trIdKey]) mK') ∧
       σ'.heap (refField σ r ltKey) =
         some (.list .arrayList (listOf σ (refField σ r ltKey) ++ [.ref y]) mT') ∧ σ.next ≤ y ∧
       σ'.heap y = some (.plain "Cbtrn02c$TranRecord" fsy) ∧ SameFields trKeys fsy (fieldsOf σ wT) ∧
       FrameS σ σ' [lK, refField σ r ltKey] ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

theorem writeTransaction_sat : Sat Gen.prog writeTransactionRef writeTransactionSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [wtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact findKeyF_ok
    · exact copyTranF_ok
    · exact abend_ok)) writeTransaction_vc

theorem writeTransactionF_sat : Sat Gen.prog writeTransactionRef writeTransactionSpecF := by
  refine sat_weaken writeTransaction_sat (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨r0, wT0, lK0, fsR, lT, fsT, sId, idcs, ks, mK, ts, mT, hargs, hr, hlT, hwT, -, hid, -,
    hlK, -, -, -, hlTo, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro r wT lK he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨h0, y, fsy, mK', mT', h1, h2, h3, h4, h5, h6, h7⟩ :=
      hpost r0 wT0 lK0 fsR lT fsT sId ks mK ts mT hargs hr hlT hwT hid hlK hlTo
    rw [listOf_of hlK, fld_of hwT hid, refField_of hr hlT, listOf_of hlTo, fieldsOf_of hwT]
    exact ⟨h0, y, fsy, mK', mT', h1, h2, h3, h4, h5, h6, h7⟩
  | exc e σ' => exact hpost
  | wrong m => exact hpost

end EquivLean.Modernize.Cbtrn02c.Java
