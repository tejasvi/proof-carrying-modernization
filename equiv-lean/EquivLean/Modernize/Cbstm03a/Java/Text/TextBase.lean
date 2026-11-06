import EquivLean.Modernize.Cbstm03a.Java.Text.Callees

/-!
# CBSTM03A → Java: the record-text methods, common part

The contracts with fixed ghost values (`trnxTextSpecG`, …), heaps that only grow (`txt_grows`), and `Iface3`'s
`zs` text as `Iface1`'s (`zsI_eq`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun x hx => State.heap_alloc_of_lt hx o⟩

theorem grows_alloc' {σ0 σ : State} {o : Obj} (h : Grows σ0 σ) : Grows σ0 (σ.alloc o).2 :=
  grows_trans h (grows_alloc σ o)

theorem grows_k' {σ0 σ σ' : State} (h : Grows σ0 σ) (hk : GrowsK σ σ') : Grows σ0 σ' :=
  grows_trans h (growsK_elim hk)

theorem growsK_of {σ σ' : State} (h : Grows σ σ') : GrowsK σ σ' := by unfold GrowsK; exact h

/-- `Grows σ0 σ` for a state built from `σ0` by allocations and callees (`GrowsK`); reflexivity last. -/
macro "txt_grows" : tactic => `(tactic| repeat (first | refine grows_alloc' ?_ | refine grows_k' ?_ (by assumption) | exact grows_refl _))

theorem zsLast_eq (neg : Bool) (d : Nat) : zsLast neg d = ovpChar neg d := by
  unfold zsLast ovpChar
  cases neg <;> by_cases h : d = 0 <;> simp [h]

/-- `Iface3`'s `zs` text is `Iface1`'s. -/
theorem zsI_eq (v : Int) (n : Nat) : zsI v n = zsStr v n := by
  simp only [zsI, zsStr, zsLast_eq]

def trnxTextSpecG (v : Value) (t : Option TrnxR) : Spec := Spec.of
  (fun args σ => args = [v] ∧ TrnxAtN σ v t ∧ σ.initOf "Cbstm03a" = .done)
  (fun _ σ r σ' => ∃ y, r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.str (trnxTextO t)) ∧
     Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def xrefTextSpecG (v : Value) (t : Option XrefR) : Spec := Spec.of
  (fun args σ => args = [v] ∧ XrefAtN σ v t ∧ σ.initOf "Cbstm03a" = .done)
  (fun _ σ r σ' => ∃ y, r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.str (xrefTextO t)) ∧
     Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def custTextSpecG (v : Value) (t : Option CustR) : Spec := Spec.of
  (fun args σ => args = [v] ∧ CustAtN σ v t ∧ σ.initOf "Cbstm03a" = .done)
  (fun _ σ r σ' => ∃ y, r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.str (custTextO t)) ∧
     Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def acctTextSpecG (v : Value) (t : Option AcctR) : Spec := Spec.of
  (fun args σ => args = [v] ∧ AcctAtN σ v t ∧ σ.initOf "Cbstm03a" = .done)
  (fun _ σ r σ' => ∃ y, r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.str (acctTextO t)) ∧
     Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

end EquivLean.Modernize.Cbstm03a.Java.Txt
