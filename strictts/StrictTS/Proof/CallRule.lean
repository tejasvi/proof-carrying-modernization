/-
StrictTS proof layer: the call rule over an abstract program.

A call runs the body of whatever definition the program has at the reference's index, so a
proof about one function needs only that function's definition and the fact that the program
contains it (`callFun_lookup`), not the rest of the program. This file imports only the
semantics, so that the per-function modules of the translator's modular output
(`--modular`, `f_call_of`) stay cheap to load; `StrictTS.Proof.Contract` re-exports it.
-/
import StrictTS.Core.Sem

namespace StrictTS

variable {TT : TypeTable}

/-- **Call rule over an abstract program**: a call runs the body of whatever definition the
program has at the reference's index, provided its signature matches. -/
theorem callFun_of_lookup (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} (f : FunRef args ret)
    (d : FunDef TT) (hd : P.funs[f.idx]? = some d) (h : d.args = args ∧ d.ret = ret)
    (vs : Vals TT args.toList) :
    callFun I P f vs = applyLam I P (h.1 ▸ h.2 ▸ d.lam) .nil vs := by
  rw [callFun.eq_1]
  simp only [hd]
  rw [dite_eq_left_of_eq_true (eq_true h)]

/-- The call rule for a definition with the reference's own signature (the form emitted for
modular proofs: `hd` is the only fact about the rest of the program). -/
theorem callFun_lookup (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} (f : FunRef args ret)
    (name : String) (lam : Lam TT args ret []) (hd : P.funs[f.idx]? = some ⟨name, args, ret, lam⟩)
    (vs : Vals TT args.toList) :
    callFun I P f vs = applyLam I P lam .nil vs :=
  callFun_of_lookup I P f _ hd ⟨rfl, rfl⟩ vs

/-! Lookup facts in constant time per function: the modular output defines the function list
by its suffixes (`funs_k := d_k :: funs_(k+1)`) and derives `program.funs.drop k = funs_k` from
the fact for `k - 1`, so that no proof indexes into the whole list. -/

theorem drop_succ_of_drop_eq {α : Type _} {l : List α} {k : Nat} {a : α} {rest : List α}
    (h : l.drop k = a :: rest) : l.drop (k + 1) = rest := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero => simp only [List.drop_zero, List.cons.injEq] at h; simp [h.2]
    | succ k => simp only [List.drop_succ_cons] at h ⊢; exact ih h

theorem getElem?_of_drop_eq {α : Type _} {l : List α} {k : Nat} {a : α} {rest : List α}
    (h : l.drop k = a :: rest) : l[k]? = some a := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero => simp only [List.drop_zero, List.cons.injEq] at h; simp [h.1]
    | succ k => simp only [List.drop_succ_cons] at h; simp [ih h]

end StrictTS
