import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMS

/-!
# CBTRN02C → Java: the model state along the daily transactions

`G.st (k + 1)` is one more step; each step adds at most one element to each list (the bounds
`LB`); the transaction records written are those of earlier transactions (`TranIds`).
-/

open EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem G.st_succ (g : G) {k : Nat} (hk : k < g.trans.length) :
    g.st (k + 1) = g.step (g.st k) (g.trec k) := by
  simp only [G.st, G.trec]
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem G.st_length (g : G) : g.st g.trans.length = g.trans.foldl g.step (Model.init g.accts g.cats) := by
  simp only [G.st, List.take_length]

theorem replaceFirst_length {α : Type} (p : α → Bool) (x : α) :
    ∀ l : List α, (Model.replaceFirst p x l).length = l.length
  | [] => rfl
  | y :: ys => by
    simp only [Model.replaceFirst]
    split
    · rfl
    · simp only [List.length_cons, replaceFirst_length p x ys]

/-- The lengths of the lists after `k` transactions. -/
def LB (s : Model.St) (c0 k : Nat) : Prop :=
  s.tranW.length ≤ k ∧ s.rejW.length ≤ k ∧ s.catW.length ≤ k ∧ s.catRW.length ≤ k ∧
  s.acctRW.length ≤ k ∧ s.disp.length ≤ k + 1 ∧ s.rejects ≤ k ∧ s.cats.length ≤ c0 + k

theorem LB.init (accts cats : List (List FVal)) : LB (Model.init accts cats) cats.length 0 := by
  simp [LB, Model.init]

theorem LB.reject {s : Model.St} {c0 k : Nat} (h : LB s c0 k) (t : List FVal) (code : Int)
    (desc : List UInt8) : LB (s.reject t code desc) c0 (k + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [LB, Model.St.reject, List.length_append, List.length_singleton]
  omega

theorem LB.post {s : Model.St} {c0 k : Nat} (h : LB s c0 k) (clk : List UInt8) (t x a : List FVal) :
    LB (s.post clk t x a) c0 (k + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rw [post_eq]
  unfold postTr postAcc postCat
  split <;> simp only [LB, List.length_append, List.length_singleton] <;>
    first
    | omega
    | (refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
       rw [replaceFirst_length]; omega)

theorem LB.step {s : Model.St} {c0 k : Nat} (h : LB s c0 k) (xrefs : List (List FVal))
    (clk : List UInt8) (t : List FVal) : LB (Model.step xrefs clk s t) c0 (k + 1) := by
  by_cases hv : vreason xrefs s.accts t = 0
  · obtain ⟨x, a, -, -, he⟩ := step_post xrefs clk s t hv
    rw [he]; exact h.post clk t x a
  · rw [step_reject xrefs clk s t hv]; exact h.reject t _ _

theorem G.lb (g : G) {k : Nat} (hk : k ≤ g.trans.length) : LB (g.st k) g.cats.length k := by
  induction k with
  | zero => simp only [G.st, List.take_zero, List.foldl_nil]; exact LB.init _ _
  | succ k ih =>
    rw [G.st_succ g (by omega)]
    exact (ih (by omega)).step _ _ _

/-- The transaction records written after `k` transactions are those of earlier transactions. -/
def TranIds (g : G) (s : Model.St) (k : Nat) : Prop :=
  ∀ r ∈ s.tranW, ∃ j, j < k ∧ r = Model.tranVals (g.trec j) g.clk

theorem G.tranIds (g : G) {k : Nat} (hk : k ≤ g.trans.length) : TranIds g (g.st k) k := by
  induction k with
  | zero => simp [TranIds, G.st, Model.init]
  | succ k ih =>
    rw [G.st_succ g (by omega)]
    have ih' := ih (by omega)
    intro r hr
    simp only [G.step] at hr
    by_cases hv : vreason g.xrefs (g.st k).accts (g.trec k) = 0
    · obtain ⟨x, a, -, -, he⟩ := step_post g.xrefs g.clk (g.st k) (g.trec k) hv
      rw [he, post_eq] at hr
      unfold postTr postAcc postCat at hr
      split at hr <;>
      · simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · obtain ⟨j, hj, rfl⟩ := ih' r hr
          exact ⟨j, by omega, rfl⟩
        · exact ⟨k, by omega, rfl⟩
    · rw [step_reject g.xrefs g.clk (g.st k) (g.trec k) hv] at hr
      obtain ⟨j, hj, rfl⟩ := ih' r hr
      exact ⟨j, by omega, rfl⟩

end EquivLean.Modernize.Cbtrn02c.Java
