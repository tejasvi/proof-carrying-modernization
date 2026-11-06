import EquivLean.Modernize.Cbact04c.JavaRunRunLemmas
import EquivLean.Modernize.Cbact04c.JavaRunModelInv

/-!
# CBACT04C → Java: one model step in the phases of `run`'s loop body, and what holds along the fold

* `step_eq`: `Model.step` is the account part `stSel` followed by the interest part `stFin`;
* `StInv`: the account table keeps its ids and groups and stays valid, the current account and
  cross-reference are the lookups of the last account id, the total and the suffix stay in range.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- **One category record**: the account part, then the interest part at the rate of the
account's group. -/
theorem step_eq (xrefs discs : List (List FV)) (parm clk : List UInt8) (s : Model.St)
    (t : List FV) :
    Model.step xrefs discs parm clk s t =
      stFin parm clk (Model.findRate discs (Model.aGrp (stSel xrefs s t).acct) (Model.tType t)
        (Model.tCat t)) (stSel xrefs s t) t := by
  by_cases h : s.lastId = some (Model.tAcct t)
  · simp only [Model.step, stFin, stSel, disp1, h, ↓reduceIte]
  · cases hl : s.lastId with
    | none =>
      have h' : ¬ (none : Option Int) = some (Model.tAcct t) := by simp
      simp only [Model.step, stFin, stSel, stAcct, stRw, disp1, hl, h', ↓reduceIte,
        Option.isSome_none, Bool.false_eq_true]
    | some id =>
      rw [hl] at h
      simp only [Model.step, stFin, stSel, stAcct, stRw, disp1, hl, h, ↓reduceIte,
        Option.isSome_some]

end EquivLean.Modernize.Cbact04c.Java
