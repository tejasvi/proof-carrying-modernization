import EquivLean.Modernize.Cbstm03a.Java.Text.TextBase

/-!
# CBSTM03A → Java: closing the postconditions of `writeTrans` and `createStatement`

Strings stay along a path (`txt_strmono`: updates of objects that are not strings, allocations, callees), so each
new line of a list holds the text its `fix` call gave (`heap_of_strMono_eq`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

theorem heap_of_strMono_eq {σ σ' : State} {x : Addr} {s s' : JStr} (h : σ.heap x = some (.str s))
    (hm : StrMono σ σ') (he : s = s') : σ'.heap x = some (.str s') := he ▸ hm x s h

theorem strMono_step_setObj {σ0 σ : State} {l : Addr} {o : Obj} (h : StrMono σ0 σ)
    (hl : ∀ s, σ.heap l ≠ some (.str s)) : StrMono σ0 (σ.setObj l o) :=
  strMono_trans h (strMono_setObj hl)

theorem strMono_step_alloc {σ0 σ : State} {o : Obj} (h : StrMono σ0 σ) : StrMono σ0 (σ.alloc o).2 :=
  strMono_trans h (strMono_alloc σ o)

theorem strMono_step_growsK {σ0 σ σ' : State} (h : StrMono σ0 σ) (hk : GrowsK σ σ') : StrMono σ0 σ' :=
  strMono_trans h (strMono_of_grows (growsK_elim hk))

/-- `StrMono σ0 σ` for a state built from `σ0` by updates of objects that are not strings (the update's address
looked up with `hsimpK`), allocations and callees (`GrowsK`). -/
macro "txt_strmono" : tactic => `(tactic| repeat (first | (refine strMono_step_setObj ?_ (by intro s; hsimpK; simp)) | (refine strMono_step_alloc ?_) | (refine strMono_step_growsK ?_ (by assumption)) | exact strMono_refl _))

end EquivLean.Modernize.Cbstm03a.Java.Txt
