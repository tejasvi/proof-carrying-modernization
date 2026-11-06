/-
StrictTS proof layer: loop summarization.

A `for (const x of arr)` loop whose body always completes normally is the left fold of the
body's effect over the elements. `evalForOf_summary` states this for a step function `F`
given as a parameter; the tactic `ts_summarize` (below) computes `F` itself by symbolically
executing the body once on a generic state, so no loop invariant has to be written. Counted
loops `for (let i = k0; i < n; i++)` are folds over the positions (`evalLoop_count_pure`, …).
-/
import StrictTS.Proof.Tactics
import StrictTS.Proof.LibLemmas
import StrictTS.Proof.CallbacksAt

namespace StrictTS
open JS

variable {TT : TypeTable}

/-- The state after running a step function over a list of elements. -/
def foldEff {Γ : Ctx} {t : Ty} (F : Val TT t → Env TT Γ → World TT → Env TT Γ × World TT)
    (xs : List (Val TT t)) (env : Env TT Γ) (w : World TT) : Env TT Γ × World TT :=
  xs.foldl (fun s x => F x s.1 s.2) (env, w)

@[simp] theorem foldEff_nil {Γ : Ctx} {t : Ty} (F : Val TT t → Env TT Γ → World TT → Env TT Γ × World TT)
    (env : Env TT Γ) (w : World TT) : foldEff F [] env w = (env, w) := rfl

@[simp] theorem foldEff_cons {Γ : Ctx} {t : Ty} (F : Val TT t → Env TT Γ → World TT → Env TT Γ × World TT)
    (x : Val TT t) (xs : List (Val TT t)) (env : Env TT Γ) (w : World TT) :
    foldEff F (x :: xs) env w = foldEff F xs (F x env w).1 (F x env w).2 := rfl

theorem evalForOf_summary_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    (Pre : World TT → Prop) (F : Val TT t → Env TT Γ → World TT → Env TT Γ × World TT)
    (hcell : ∀ w, Pre w → w.heap.get? (.arr t, a) = some xs)
    (hF : ∀ x env w, Pre w →
      exec (evalB I P body (.cons x env)) w = some (.ok (.normal, .cons x (F x env w).1), (F x env w).2))
    (hPre : ∀ x env w, Pre w → Pre (F x env w).2) :
    ∀ (n i : Nat) (env : Env TT Γ) (w : World TT), xs.size - i = n → Pre w →
      exec (evalForOf I P a i body env) w =
        some (.ok (.normal, (foldEff F (xs.toList.drop i) env w).1), (foldEff F (xs.toList.drop i) env w).2) := by
  intro n
  induction n with
  | zero =>
    intro i env w hn hw
    have hle : xs.size ≤ i := by omega
    have hdrop : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hle)
    rw [evalForOf.eq_1]
    simp [hcell _ hw, hdrop, Nat.not_lt.mpr hle]
  | succ n ih =>
    intro i env w hn hw
    have hlt : i < xs.size := by omega
    have hdrop : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [evalForOf.eq_1]
    simp only [exec_bind, exec_readArr, hcell _ hw, hlt, dite_true, hF _ _ _ hw, hdrop, foldEff_cons,
      Env.tail_cons]
    exact ih (i + 1) _ _ (by omega) (hPre _ _ _ hw)

/-- **Loop summarization.** A `for (const x of arr)` loop over an array holding `xs`, whose
body completes normally with effect `F` on every state satisfying `Pre` (and keeps `Pre`), is
the fold of `F` over `xs`. -/
theorem evalForOf_summary (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    (Pre : World TT → Prop) (F : Val TT t → Env TT Γ → World TT → Env TT Γ × World TT)
    (hcell : ∀ w, Pre w → w.heap.get? (.arr t, a) = some xs)
    (hF : ∀ x env w, Pre w →
      exec (evalB I P body (.cons x env)) w = some (.ok (.normal, .cons x (F x env w).1), (F x env w).2))
    (hPre : ∀ x env w, Pre w → Pre (F x env w).2) (env : Env TT Γ) (w : World TT) (hw : Pre w) :
    exec (evalForOf I P a 0 body env) w =
      some (.ok (.normal, (foldEff F xs.toList env w).1), (foldEff F xs.toList env w).2) := by
  simpa using evalForOf_summary_aux I P body a xs Pre F hcell hF hPre (xs.size - 0) 0 env w rfl hw

/-- Loop summarization with the step function split into its effect on the environment
(`FE`) and on the world (`FW`); in this form `ts_summarize` lets the unifier read both off the
symbolic execution of the body. Only the loop's array cell needs to be preserved. -/
theorem evalForOf_summary2 (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    (FE : Val TT t → Env TT Γ → World TT → Env TT Γ) (FW : Val TT t → Env TT Γ → World TT → World TT)
    (hF : ∀ x env w, w.heap.get? (.arr t, a) = some xs →
      exec (evalB I P body (.cons x env)) w = some (.ok (.normal, .cons x (FE x env w)), FW x env w))
    (hkeep : ∀ x env w, w.heap.get? (.arr t, a) = some xs → (FW x env w).heap.get? (.arr t, a) = some xs)
    (env : Env TT Γ) (w : World TT) (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalForOf I P a 0 body env) w =
      some (.ok (.normal, (foldEff (fun x e w => (FE x e w, FW x e w)) xs.toList env w).1),
        (foldEff (fun x e w => (FE x e w, FW x e w)) xs.toList env w).2) :=
  evalForOf_summary I P body a xs (fun w => w.heap.get? (.arr t, a) = some xs) _ (fun _ h => h)
    (fun x env w h => by rw [hF x env w h]) (fun x env w h => hkeep x env w h) env w hw

/-- A fold whose steps leave the world unchanged is a fold over environments. -/
theorem foldEff_world_const {Γ : Ctx} {t : Ty} (FE : Val TT t → Env TT Γ → World TT → Env TT Γ)
    (xs : List (Val TT t)) (env : Env TT Γ) (w : World TT) :
    foldEff (fun x e w => (FE x e w, w)) xs env w = (xs.foldl (fun e x => FE x e w) env, w) := by
  induction xs generalizing env with
  | nil => rfl
  | cons x xs ih => simp only [foldEff_cons]; rw [ih]; rfl

/-- Projection of a fold: if `p` of a step depends only on `p` of the state, `p` of the fold
is a fold of that dependence (fold fusion). -/
theorem foldl_proj {α β σ : Type} (p : α → σ) (f : α → β → α) (g : σ → β → σ)
    (hpf : ∀ s x, p (f s x) = g (p s) x) (xs : List β) (s : α) :
    p (xs.foldl f s) = xs.foldl g (p s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, hpf]

/-! ### Slot-wise summaries

The tactic encodes the loop's environment by the values of its **mutable** slots (`σ` is
their product; `const` slots never change) and reads the step function off the symbolic
execution of the body, one component per mutable slot. -/

/-- Completions after which a `for … of` loop goes on with the next element. -/
def Completion.isNext {ρ : Ty} : Completion TT ρ → Bool
  | .normal => true
  | .cont 0 => true
  | _ => false

@[simp] theorem Completion.isNext_normal {ρ : Ty} : (Completion.normal : Completion TT ρ).isNext = true := rfl
@[simp] theorem Completion.isNext_cont0 {ρ : Ty} : (Completion.cont 0 : Completion TT ρ).isNext = true := rfl
@[simp] theorem Completion.isNext_ite {ρ : Ty} (c : Prop) [Decidable c] (a b : Completion TT ρ) :
    (if c then a else b).isNext = (if c then a.isNext else b.isNext) := by
  split <;> rfl

theorem Completion.eq_of_isNext {ρ : Ty} {c : Completion TT ρ} (h : c.isNext = true) :
    c = .normal ∨ c = .cont 0 := by
  match c, h with
  | .normal, _ => exact Or.inl rfl
  | .cont 0, _ => exact Or.inr rfl

theorem evalForOf_summary_enc_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ : Type} (enc : σ → Env TT Γ) (Pre : World TT → Prop)
    (C : Val TT t → σ → World TT → Completion TT ρ)
    (G : Val TT t → σ → World TT → σ) (GW : Val TT t → σ → World TT → World TT)
    (hcell : ∀ w, Pre w → w.heap.get? (.arr t, a) = some xs)
    (hC : ∀ x s w, Pre w → (C x s w).isNext = true)
    (hF : ∀ x s w, Pre w →
      exec (evalB I P body (.cons x (enc s))) w = some (.ok (C x s w, .cons x (enc (G x s w))), GW x s w))
    (hPre : ∀ x s w, Pre w → Pre (GW x s w)) :
    ∀ (n i : Nat) (s : σ) (w : World TT), xs.size - i = n → Pre w →
      exec (evalForOf I P a i body (enc s)) w =
        some (.ok (.normal, enc ((xs.toList.drop i).foldl (fun p x => (G x p.1 p.2, GW x p.1 p.2)) (s, w)).1),
          ((xs.toList.drop i).foldl (fun p x => (G x p.1 p.2, GW x p.1 p.2)) (s, w)).2) := by
  intro n
  induction n with
  | zero =>
    intro i s w hn hw
    have hle : xs.size ≤ i := by omega
    have hdrop : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hle)
    rw [evalForOf.eq_1]
    simp [hcell _ hw, hdrop, Nat.not_lt.mpr hle]
  | succ n ih =>
    intro i s w hn hw
    have hlt : i < xs.size := by omega
    have hdrop : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [evalForOf.eq_1]
    simp only [exec_bind, exec_readArr, hcell _ hw, hlt, dite_true, hF _ _ _ hw, hdrop, List.foldl_cons,
      Env.tail_cons]
    rcases Completion.eq_of_isNext (hC xs[i] s w hw) with h | h <;> rw [h] <;>
      exact ih (i + 1) _ _ (by omega) (hPre _ _ _ hw)

/-- A fold over pairs whose second component never changes. -/
theorem foldl_pair_const {α β γ : Type} (f : β → α → α) (l : List β) (a : α) (c : γ) :
    l.foldl (fun p x => (f x p.1, p.2)) (a, c) = (l.foldl (fun a x => f x a) a, c) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => exact ih (f x a)

/-- **Loop summarization, world unchanged.** If one iteration of the body, from any value
`s` of the mutable slots, completes normally with new values `G x s` and leaves the world
as it was, the loop is the left fold of `G`. -/
theorem evalForOf_summary_pure (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ : Type} (enc : σ → Env TT Γ) (C : Val TT t → σ → Completion TT ρ) (G : Val TT t → σ → σ) (s0 : σ)
    (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw : w.heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s, exec (evalB I P body (.cons x (enc s))) w = some (.ok (C x s, .cons x (enc (G x s))), w))
    (hC : ∀ x s, (C x s).isNext = true) :
    exec (evalForOf I P a 0 body env) w = some (.ok (.normal, enc (xs.toList.foldl (fun s x => G x s) s0)), w) := by
  subst henv
  have h := evalForOf_summary_enc_aux I P body a xs enc (· = w) (fun x s _ => C x s) (fun x s _ => G x s)
    (fun _ _ w' => w') (fun w' h => h ▸ hw) (fun x s _ _ => hC x s) (fun x s w' h => h ▸ hF x s)
    (fun _ _ _ h => h) (xs.size - 0) 0 s0 w rfl rfl
  simp only [List.drop_zero, foldl_pair_const] at h
  exact h

/-- **Loop summarization, world changed.** The general form: the iteration state is the
values of the mutable slots and the world; `Pre` (which must fix the loop's array) is kept by
every iteration. -/
theorem evalForOf_summary_world (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ : Type} (enc : σ → Env TT Γ) (Pre : World TT → Prop) (C : Val TT t → σ → World TT → Completion TT ρ)
    (G : Val TT t → σ → World TT → σ) (GW : Val TT t → σ → World TT → World TT)
    (s0 : σ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw : Pre w)
    (hcell : ∀ w, Pre w → w.heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s w, Pre w →
      exec (evalB I P body (.cons x (enc s))) w = some (.ok (C x s w, .cons x (enc (G x s w))), GW x s w))
    (hC : ∀ x s w, Pre w → (C x s w).isNext = true)
    (hPre : ∀ x s w, Pre w → Pre (GW x s w)) :
    exec (evalForOf I P a 0 body env) w =
      some (.ok (.normal, enc (xs.toList.foldl (fun p x => (G x p.1 p.2, GW x p.1 p.2)) (s0, w)).1),
        (xs.toList.foldl (fun p x => (G x p.1 p.2, GW x p.1 p.2)) (s0, w)).2) := by
  subst henv
  simpa using evalForOf_summary_enc_aux I P body a xs enc Pre C G GW hcell hC hF hPre (xs.size - 0) 0 s0 w rfl hw

/-! Path merging: a conditional whose branches have the same shape is pushed inside, so that
the effect of a body with symbolic conditions is again one state (with `if`s in its slots). -/
namespace Merge
theorem ite_some {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by split <;> rfl
theorem ite_pair {α β : Type} (c : Prop) [Decidable c] (a a' : α) (b b' : β) :
    (if c then (a, b) else (a', b')) = (if c then a else a', if c then b else b') := by split <;> rfl
theorem ite_ok {ε α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (Except.ok a : Except ε α) else Except.ok b) = Except.ok (if c then a else b) := by split <;> rfl
theorem ite_cons {s : Slot} {Γ : Ctx} (c : Prop) [Decidable c] (a b : Val TT s.ty) (e e' : Env TT Γ) :
    (if c then Env.cons a e else Env.cons b e') = Env.cons (if c then a else b) (if c then e else e') := by
  split <;> rfl
theorem split_ite {α : Sort _} {c : Prop} [Decidable c] {a : α} : a = if c then a else a := (ite_self a).symm
/-- A negated Boolean test is the swapped conditional (normal form for comparing two programs
whose tests are negations of each other). -/
@[simp] theorem ite_eq_false_swap {α : Sort _} (b : Bool) (x y : α) :
    (if b = false then x else y) = (if b = true then y else x) := by
  cases b <;> rfl

/-- Case analysis on an optional value, as one term (the merge of the two paths of a `match`). -/
def optCase {α β : Type} (d : Option α) (a : β) (b : α → β) : β :=
  match d with
  | none => a
  | some v => b v

@[simp] theorem optCase_none {α β : Type} (a : β) (b : α → β) : optCase none a b = a := rfl
@[simp] theorem optCase_some {α β : Type} (v : α) (a : β) (b : α → β) : optCase (some v) a b = b v := rfl
@[simp] theorem optCase_const {α β : Type} (d : Option α) (a : β) : optCase d a (fun _ => a) = a := by
  cases d <;> rfl
theorem split_opt {α β : Type} {d : Option α} {a : β} : a = optCase d a (fun _ => a) := by
  cases d <;> rfl
theorem optCase_congr {α β : Type} {d : Option α} {a a' : β} {b b' : α → β} (h1 : d = none → a = a')
    (h2 : ∀ v, d = some v → b v = b' v) : optCase d a b = optCase d a' b' := by
  cases h : d with
  | none => exact h1 h
  | some v => exact h2 v h
theorem ite_congr' {α : Sort _} {c : Prop} [Decidable c] {a b a' b' : α} (h1 : c → a = a') (h2 : ¬c → b = b') :
    (if c then a else b) = (if c then a' else b') := by
  by_cases h : c
  · simp only [h, ite_true, h1 h]
  · simp only [h, ite_false, h2 h]
end Merge

theorem evalForOf_summary_cells_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (hcell : ∀ c, (put c).heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNext = true) :
    ∀ (n i : Nat) (s : σ) (c : κ), xs.size - i = n →
      exec (evalForOf I P a i body (enc s)) (put c) =
        some (.ok (.normal, enc ((xs.toList.drop i).foldl (fun p x => (G x p.1 p.2, H x p.1 p.2)) (s, c)).1),
          put ((xs.toList.drop i).foldl (fun p x => (G x p.1 p.2, H x p.1 p.2)) (s, c)).2) := by
  intro n
  induction n with
  | zero =>
    intro i s c hn
    have hle : xs.size ≤ i := by omega
    have hdrop : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hle)
    rw [evalForOf.eq_1]
    simp [hcell c, hdrop, Nat.not_lt.mpr hle]
  | succ n ih =>
    intro i s c hn
    have hlt : i < xs.size := by omega
    have hdrop : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [evalForOf.eq_1]
    simp only [exec_bind, exec_readArr, hcell c, hlt, dite_true, hF, hdrop, List.foldl_cons, Env.tail_cons]
    rcases Completion.eq_of_isNext (hC xs[i] s c) with h | h <;> rw [h] <;>
      exact ih (i + 1) _ _ (by omega)

/-- **Loop summarization, cells written.** The world of every iteration is `put c` (the world
at the loop with the written cells holding `c`); the state of the fold is the values of the
mutable variables and the cells' contents. -/
theorem evalForOf_summary_cells (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNext = true) :
    exec (evalForOf I P a 0 body env) w =
      some (.ok (.normal, enc (xs.toList.foldl (fun p x => (G x p.1 p.2, H x p.1 p.2)) (s0, c0)).1),
        put (xs.toList.foldl (fun p x => (G x p.1 p.2, H x p.1 p.2)) (s0, c0)).2) := by
  subst henv hw0
  simpa using evalForOf_summary_cells_aux I P body a xs enc put C G H hcell hF hC (xs.size - 0) 0 s0 c0 rfl

/-! ### Loops with `break`

The fold carries a flag: once an iteration ends with `break`, the remaining elements change
nothing (the state after the breaking iteration is kept, as JavaScript does). -/

/-- `break` out of the innermost loop. -/
def Completion.isBrk0 {ρ : Ty} : Completion TT ρ → Bool
  | .brk 0 => true
  | _ => false

/-- Completions a `for … of` body may end with when summarized: go on, or leave the loop. -/
def Completion.isNextOrBrk {ρ : Ty} (c : Completion TT ρ) : Bool := c.isNext || c.isBrk0

@[simp] theorem Completion.isNextOrBrk_normal {ρ : Ty} : (Completion.normal : Completion TT ρ).isNextOrBrk = true := rfl
@[simp] theorem Completion.isNextOrBrk_cont0 {ρ : Ty} : (Completion.cont 0 : Completion TT ρ).isNextOrBrk = true := rfl
@[simp] theorem Completion.isNextOrBrk_brk0 {ρ : Ty} : (Completion.brk 0 : Completion TT ρ).isNextOrBrk = true := rfl
@[simp] theorem Completion.isNextOrBrk_ite {ρ : Ty} (c : Prop) [Decidable c] (a b : Completion TT ρ) :
    (if c then a else b).isNextOrBrk = (if c then a.isNextOrBrk else b.isNextOrBrk) := by
  split <;> rfl
@[simp] theorem Completion.isBrk0_normal {ρ : Ty} : (Completion.normal : Completion TT ρ).isBrk0 = false := rfl
@[simp] theorem Completion.isBrk0_cont0 {ρ : Ty} : (Completion.cont 0 : Completion TT ρ).isBrk0 = false := rfl
@[simp] theorem Completion.isBrk0_brk0 {ρ : Ty} : (Completion.brk 0 : Completion TT ρ).isBrk0 = true := rfl
@[simp] theorem Completion.isBrk0_ite {ρ : Ty} (c : Prop) [Decidable c] (a b : Completion TT ρ) :
    (if c then a else b).isBrk0 = (if c then a.isBrk0 else b.isBrk0) := by
  split <;> rfl

theorem Completion.cases_of_isNextOrBrk {ρ : Ty} {c : Completion TT ρ} (h : c.isNextOrBrk = true) :
    c = .normal ∨ c = .cont 0 ∨ c = .brk 0 := by
  match c, h with
  | .normal, _ => exact Or.inl rfl
  | .cont 0, _ => exact Or.inr (Or.inl rfl)
  | .brk 0, _ => exact Or.inr (Or.inr rfl)

/-- The flagged step of a loop with `break`. -/
def brkStep {α σ κ : Type} (B : α → σ → κ → Bool) (G : α → σ → κ → σ) (H : α → σ → κ → κ)
    (p : Bool × σ × κ) (x : α) : Bool × σ × κ :=
  if p.1 then p else (B x p.2.1 p.2.2, G x p.2.1 p.2.2, H x p.2.1 p.2.2)

theorem foldl_brkStep_done {α σ κ : Type} (B : α → σ → κ → Bool) (G : α → σ → κ → σ) (H : α → σ → κ → κ)
    (l : List α) (s : σ) (c : κ) : l.foldl (brkStep B G H) (true, s, c) = (true, s, c) := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [brkStep] using ih

theorem evalForOf_summary_brk_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (hcell : ∀ c, (put c).heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrBrk = true) :
    ∀ (n i : Nat) (s : σ) (c : κ), xs.size - i = n →
      exec (evalForOf I P a i body (enc s)) (put c) =
        some (.ok (.normal, enc ((xs.toList.drop i).foldl (brkStep (fun x s c => (C x s c).isBrk0) G H)
            (false, s, c)).2.1),
          put ((xs.toList.drop i).foldl (brkStep (fun x s c => (C x s c).isBrk0) G H) (false, s, c)).2.2) := by
  intro n
  induction n with
  | zero =>
    intro i s c hn
    have hle : xs.size ≤ i := by omega
    have hdrop : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hle)
    rw [evalForOf.eq_1]
    simp [hcell c, hdrop, Nat.not_lt.mpr hle]
  | succ n ih =>
    intro i s c hn
    have hlt : i < xs.size := by omega
    have hdrop : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [evalForOf.eq_1]
    simp only [exec_bind, exec_readArr, hcell c, hlt, dite_true, hF, hdrop, List.foldl_cons, Env.tail_cons]
    rcases Completion.cases_of_isNextOrBrk (hC xs[i] s c) with h | h | h <;> rw [h]
    · simpa [brkStep, h] using ih (i + 1) (G xs[i] s c) (H xs[i] s c) (by omega)
    · simpa [brkStep, h] using ih (i + 1) (G xs[i] s c) (H xs[i] s c) (by omega)
    · simp [brkStep, h, foldl_brkStep_done]

/-- **Loop summarization with `break`**, world unchanged. -/
theorem evalForOf_summary_pure_brk (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ : Type} (enc : σ → Env TT Γ) (C : Val TT t → σ → Completion TT ρ) (G : Val TT t → σ → σ) (s0 : σ)
    (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw : w.heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s, exec (evalB I P body (.cons x (enc s))) w = some (.ok (C x s, .cons x (enc (G x s))), w))
    (hC : ∀ x s, (C x s).isNextOrBrk = true) :
    exec (evalForOf I P a 0 body env) w =
      some (.ok (.normal, enc (xs.toList.foldl (brkStep (fun x s (_ : Unit) => (C x s).isBrk0)
        (fun x s _ => G x s) (fun _ _ _ => ())) (false, s0, ())).2.1), w) := by
  subst henv
  simpa using evalForOf_summary_brk_aux I P body a xs (κ := Unit) enc (fun _ => w) (fun x s _ => C x s)
    (fun x s _ => G x s) (fun _ _ _ => ()) (fun _ => hw) (fun x s _ => hF x s) (fun x s _ => hC x s)
    (xs.size - 0) 0 s0 () rfl

/-- **Loop summarization with `break`**, one cell written. -/
theorem evalForOf_summary_cells_brk (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrBrk = true) :
    exec (evalForOf I P a 0 body env) w =
      some (.ok (.normal, enc (xs.toList.foldl (brkStep (fun x s c => (C x s c).isBrk0) G H) (false, s0, c0)).2.1),
        put (xs.toList.foldl (brkStep (fun x s c => (C x s c).isBrk0) G H) (false, s0, c0)).2.2) := by
  subst henv hw0
  simpa using evalForOf_summary_brk_aux I P body a xs enc put C G H hcell hF hC (xs.size - 0) 0 s0 c0 rfl

/-! ### Loops with `return`

The fold carries the returned value: once an iteration returns `v`, the remaining elements
change nothing, and the loop completes with `return v` (`Completion.ofRet`); otherwise normally.
The search loops (`some`, `every`, `find` written by hand) are such folds, and the lemmas below
turn them into `List.findSome?` and then `any`/`all`/`find?`. -/

/-- The value an iteration returns, if it ends with `return`. -/
def Completion.retVal? {ρ : Ty} : Completion TT ρ → Option (Val TT ρ)
  | .ret v => some v
  | _ => none

/-- Completions a `for … of` body may end with when summarized with `return`. -/
def Completion.isNextOrRet {ρ : Ty} (c : Completion TT ρ) : Bool := c.isNext || c.retVal?.isSome

@[simp] theorem Completion.isNextOrRet_normal {ρ : Ty} : (Completion.normal : Completion TT ρ).isNextOrRet = true := rfl
@[simp] theorem Completion.isNextOrRet_cont0 {ρ : Ty} : (Completion.cont 0 : Completion TT ρ).isNextOrRet = true := rfl
@[simp] theorem Completion.isNextOrRet_ret {ρ : Ty} (v : Val TT ρ) : (Completion.ret v).isNextOrRet = true := rfl
@[simp] theorem Completion.isNextOrRet_ite {ρ : Ty} (c : Prop) [Decidable c] (a b : Completion TT ρ) :
    (if c then a else b).isNextOrRet = (if c then a.isNextOrRet else b.isNextOrRet) := by
  split <;> rfl
@[simp] theorem Completion.retVal?_normal {ρ : Ty} : (Completion.normal : Completion TT ρ).retVal? = none := rfl
@[simp] theorem Completion.retVal?_cont0 {ρ : Ty} : (Completion.cont 0 : Completion TT ρ).retVal? = none := rfl
@[simp] theorem Completion.retVal?_ret {ρ : Ty} (v : Val TT ρ) : (Completion.ret v).retVal? = some v := rfl
@[simp] theorem Completion.retVal?_ite {ρ : Ty} (c : Prop) [Decidable c] (a b : Completion TT ρ) :
    (if c then a else b).retVal? = (if c then a.retVal? else b.retVal?) := by
  split <;> rfl

theorem Completion.cases_of_isNextOrRet {ρ : Ty} {c : Completion TT ρ} (h : c.isNextOrRet = true) :
    c = .normal ∨ c = .cont 0 ∨ ∃ v, c = .ret v := by
  match c, h with
  | .normal, _ => exact Or.inl rfl
  | .cont 0, _ => exact Or.inr (Or.inl rfl)
  | .ret v, _ => exact Or.inr (Or.inr ⟨v, rfl⟩)

/-- The completion of a loop whose iterations may `return`. -/
def Completion.ofRet {ρ : Ty} : Option (Val TT ρ) → Completion TT ρ
  | some v => .ret v
  | none => .normal

@[simp] theorem Completion.ofRet_none {ρ : Ty} : Completion.ofRet (none : Option (Val TT ρ)) = .normal := rfl
@[simp] theorem Completion.ofRet_some {ρ : Ty} (v : Val TT ρ) : Completion.ofRet (some v) = .ret v := rfl

/-- The step of a loop with `return`: the first component is the returned value, if any. -/
def retStep {α β σ κ : Type} (R : α → σ → κ → Option β) (G : α → σ → κ → σ) (H : α → σ → κ → κ)
    (p : Option β × σ × κ) (x : α) : Option β × σ × κ :=
  if p.1.isSome then p else (R x p.2.1 p.2.2, G x p.2.1 p.2.2, H x p.2.1 p.2.2)

theorem foldl_retStep_done {α β σ κ : Type} (R : α → σ → κ → Option β) (G : α → σ → κ → σ)
    (H : α → σ → κ → κ) (l : List α) (v : β) (s : σ) (c : κ) :
    l.foldl (retStep R G H) (some v, s, c) = (some v, s, c) := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [retStep] using ih

/-- Without other state, the returned value is the first one found. -/
@[simp] theorem foldl_retStep_unit {α β : Type} (R : α → Unit → Unit → Option β) (G : α → Unit → Unit → Unit)
    (H : α → Unit → Unit → Unit) (l : List α) (s c : Unit) :
    l.foldl (retStep R G H) (none, s, c) = (l.findSome? (fun x => R x () ()), (), ()) := by
  suffices h : ∀ o, l.foldl (retStep R G H) (o, (), ()) = (o.or (l.findSome? (fun x => R x () ())), (), ()) by
    simpa using h none
  induction l with
  | nil => intro o; simp
  | cons x l ih =>
    intro o
    cases o with
    | some v =>
      simp only [List.foldl_cons, retStep, Option.isSome_some, ite_true]
      rw [foldl_retStep_done]
      rfl
    | none =>
      simp only [List.foldl_cons, retStep, Option.isSome_none, Bool.false_eq_true, ite_false, List.findSome?_cons,
        Option.none_or]
      rw [ih]
      cases R x () () <;> simp

@[simp high] theorem findSome?_ite_const {α β : Type} (p : α → Bool) (b : β) (l : List α) :
    l.findSome? (fun x => if p x = true then some b else none) = bif l.any p then some b else none := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x = true <;> simp [h, ih]

@[simp high] theorem findSome?_ite_const_neg {α β : Type} (p : α → Bool) (b : β) (l : List α) :
    l.findSome? (fun x => if p x = true then none else some b) = bif l.all p then none else some b := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x = true <;> simp [h, ih]

@[simp] theorem findSome?_ite_some {α β : Type} (p : α → Bool) (f : α → β) (l : List α) :
    l.findSome? (fun x => if p x = true then some (f x) else none) = (l.find? p).map f := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x = true <;> simp [h, ih]

@[simp] theorem findSome?_ite_some_neg {α β : Type} (p : α → Bool) (f : α → β) (l : List α) :
    l.findSome? (fun x => if p x = true then none else some (f x)) = (l.find? (fun x => !p x)).map f := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x = true <;> simp [h, ih]

@[simp] theorem Array.foldl_retStep_unit {α β : Type} (R : α → Unit → Unit → Option β)
    (G : α → Unit → Unit → Unit) (H : α → Unit → Unit → Unit) (xs : Array α) (s c : Unit) :
    xs.foldl (retStep R G H) (none, s, c) = (xs.findSome? (fun x => R x () ()), (), ()) := by
  rw [← Array.foldl_toList, StrictTS.foldl_retStep_unit, Array.findSome?_toList]

@[simp high] theorem Array.findSome?_ite_const {α β : Type} (p : α → Bool) (b : β) (xs : Array α) :
    xs.findSome? (fun x => if p x = true then some b else none) = bif xs.any p then some b else none := by
  rw [← Array.findSome?_toList, StrictTS.findSome?_ite_const, Array.any_toList]

@[simp high] theorem Array.findSome?_ite_const_neg {α β : Type} (p : α → Bool) (b : β) (xs : Array α) :
    xs.findSome? (fun x => if p x = true then none else some b) = bif xs.all p then none else some b := by
  rw [← Array.findSome?_toList, StrictTS.findSome?_ite_const_neg, Array.all_toList]

@[simp] theorem Array.findSome?_ite_some {α β : Type} (p : α → Bool) (f : α → β) (xs : Array α) :
    xs.findSome? (fun x => if p x = true then some (f x) else none) = (xs.find? p).map f := by
  rw [← Array.findSome?_toList, StrictTS.findSome?_ite_some, Array.find?_toList]

@[simp] theorem Array.findSome?_ite_some_neg {α β : Type} (p : α → Bool) (f : α → β) (xs : Array α) :
    xs.findSome? (fun x => if p x = true then none else some (f x)) = (xs.find? (fun x => !p x)).map f := by
  rw [← Array.findSome?_toList, StrictTS.findSome?_ite_some_neg, Array.find?_toList]

@[simp] theorem Option.elim_cond_some {α β : Type} (c : Bool) (x : α) (a : β) (f : α → β) :
    (bif c then some x else none).elim a f = bif c then f x else a := by
  cases c <;> rfl
@[simp] theorem Option.elim_cond_none {α β : Type} (c : Bool) (x : α) (a : β) (f : α → β) :
    (bif c then none else some x).elim a f = bif c then a else f x := by
  cases c <;> rfl
@[simp high] theorem Option.elim_map' {α β γ : Type} (o : Option α) (g : α → γ) (a : β) (f : γ → β) :
    (o.map g).elim a f = o.elim a (fun x => f (g x)) := by
  cases o <;> rfl
@[simp] theorem Function.lam_id_comp {α β : Type} (f : α → β) : (fun v => v) ∘ f = f := rfl
@[simp] theorem Val.cond_bool (c : Bool) :
    (bif c then (Val.bool true : Val TT .bool) else Val.bool false) = Val.bool c := by
  cases c <;> rfl
@[simp] theorem Val.cond_bool_neg (c : Bool) :
    (bif c then (Val.bool false : Val TT .bool) else Val.bool true) = Val.bool (!c) := by
  cases c <;> rfl

theorem evalForOf_summary_ret_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (hcell : ∀ c, (put c).heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrRet = true) :
    ∀ (n i : Nat) (s : σ) (c : κ), xs.size - i = n →
      exec (evalForOf I P a i body (enc s)) (put c) =
        some (.ok (Completion.ofRet ((xs.toList.drop i).foldl
              (retStep (fun x s c => (C x s c).retVal?) G H) (none, s, c)).1,
            enc ((xs.toList.drop i).foldl (retStep (fun x s c => (C x s c).retVal?) G H) (none, s, c)).2.1),
          put ((xs.toList.drop i).foldl (retStep (fun x s c => (C x s c).retVal?) G H) (none, s, c)).2.2) := by
  intro n
  induction n with
  | zero =>
    intro i s c hn
    have hle : xs.size ≤ i := by omega
    have hdrop : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hle)
    rw [evalForOf.eq_1]
    simp [hcell c, hdrop, Nat.not_lt.mpr hle]
  | succ n ih =>
    intro i s c hn
    have hlt : i < xs.size := by omega
    have hdrop : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [evalForOf.eq_1]
    simp only [exec_bind, exec_readArr, hcell c, hlt, dite_true, hF, hdrop, List.foldl_cons, Env.tail_cons]
    rcases Completion.cases_of_isNextOrRet (hC xs[i] s c) with h | h | ⟨v, h⟩ <;> rw [h]
    · simpa [retStep, h] using ih (i + 1) (G xs[i] s c) (H xs[i] s c) (by omega)
    · simpa [retStep, h] using ih (i + 1) (G xs[i] s c) (H xs[i] s c) (by omega)
    · simp [retStep, h, foldl_retStep_done]

/-- **Loop summarization with `return`**, world unchanged. -/
theorem evalForOf_summary_pure_ret (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ : Type} (enc : σ → Env TT Γ) (C : Val TT t → σ → Completion TT ρ) (G : Val TT t → σ → σ) (s0 : σ)
    (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw : w.heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s, exec (evalB I P body (.cons x (enc s))) w = some (.ok (C x s, .cons x (enc (G x s))), w))
    (hC : ∀ x s, (C x s).isNextOrRet = true) :
    exec (evalForOf I P a 0 body env) w =
      some (.ok (Completion.ofRet (xs.toList.foldl (retStep (fun x s (_ : Unit) => (C x s).retVal?)
          (fun x s _ => G x s) (fun _ _ _ => ())) (none, s0, ())).1,
        enc (xs.toList.foldl (retStep (fun x s (_ : Unit) => (C x s).retVal?)
          (fun x s _ => G x s) (fun _ _ _ => ())) (none, s0, ())).2.1), w) := by
  subst henv
  have h := evalForOf_summary_ret_aux I P body a xs (κ := Unit) enc (fun _ => w) (fun x s _ => C x s)
    (fun x s _ => G x s) (fun _ _ _ => ()) (fun _ => hw) (fun x s _ => hF x s) (fun x s _ => hC x s)
    (xs.size - 0) 0 s0 () rfl
  rw [List.drop_zero] at h
  exact h

/-- **Loop summarization with `return`**, one cell written. -/
theorem evalForOf_summary_cells_ret (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.arr t, a) = some xs)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrRet = true) :
    exec (evalForOf I P a 0 body env) w =
      some (.ok (Completion.ofRet (xs.toList.foldl (retStep (fun x s c => (C x s c).retVal?) G H) (none, s0, c0)).1,
          enc (xs.toList.foldl (retStep (fun x s c => (C x s c).retVal?) G H) (none, s0, c0)).2.1),
        put (xs.toList.foldl (retStep (fun x s c => (C x s c).retVal?) G H) (none, s0, c0)).2.2) := by
  subst henv hw0
  have h := evalForOf_summary_ret_aux I P body a xs enc put C G H hcell hF hC (xs.size - 0) 0 s0 c0 rfl
  rw [List.drop_zero] at h
  exact h

open Lean Meta in
/-- An `if` whose decidability instance was left behind by a definitional rewrite of its
condition (`dsimp` does not visit instances; e.g. `F64.gt_eq_lt` turns `x.gt y` into `y.lt x` in
the condition only): the instance is synthesized again for the current condition, so that the
fold lemmas about `if p x = true then …` match. -/
dsimproc [ts_sym] iteStaleInstance (ite _ _ _) := fun e => do
  unless e.isAppOfArity ``ite 5 do return .continue
  if e.hasLooseBVars then return .continue
  let args := e.getAppArgs
  let c := args[1]!
  let ty ← instantiateMVars (← inferType args[2]!)
  if ty.isAppOfArity ``Decidable 1 && ty.appArg!.consumeMData == c.consumeMData then return .continue
  let some inst ← (try some <$> synthInstance (mkApp (mkConst ``Decidable) c) catch _ => pure none)
    | return .continue
  return .continue (some (mkAppN e.getAppFn #[args[0]!, c, inst, args[3]!, args[4]!]))

theorem foldl_pair_unit {β κ : Type} (H : β → κ → κ) (l : List β) (c : κ) :
    l.foldl (fun p x => (((), H x p.2) : Unit × κ)) ((), c) = ((), l.foldl (fun c x => H x c) c) := by
  induction l generalizing c with
  | nil => rfl
  | cons x l ih => exact ih (H x c)

/-- **Loop summarization, one cell written, no mutable variable**: the loop is the fold of the
cell's update. -/
theorem evalForOf_summary_cell1 (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    {κ : Type} (env : Env TT Γ) (put : κ → World TT)
    (C : Val TT t → κ → Completion TT ρ) (H : Val TT t → κ → κ) (c0 : κ) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.arr t, a) = some xs)
    (hF : ∀ x c, exec (evalB I P body (.cons x env)) (put c) = some (.ok (C x c, .cons x env), put (H x c)))
    (hC : ∀ x c, (C x c).isNext = true) :
    exec (evalForOf I P a 0 body env) w = some (.ok (.normal, env), put (xs.toList.foldl (fun c x => H x c) c0)) := by
  have h := evalForOf_summary_cells I P body a xs (σ := Unit) (fun _ => env) put (fun x _ c => C x c)
    (fun _ _ _ => ()) (fun x _ c => H x c) () c0 env rfl w hw0 hcell (fun x _ c => hF x c) (fun x _ c => hC x c)
  rw [h, foldl_pair_unit]

/-- A cell that exists can be written with its own content. -/
theorem World.eq_insert_getD (w : World TT) (K : HKey) (d : K.1.Cell TT) (h : (w.heap.get? K).isSome = true) :
    w = { w with heap := w.heap.insert K ((w.heap.get? K).getD d) } := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  have : w.heap.insert K ((w.heap.get? K).getD d) = w.heap := by
    apply Std.ExtDHashMap.ext_get?
    intro K'
    rw [Std.ExtDHashMap.get?_insert]
    split
    · next heq =>
      have heq' : K = K' := by simpa using heq
      subst heq'
      simp [hc]
    · rfl
  rw [this]

/-- A world is itself with a cell rewritten with its own content. -/
theorem World.eq_insert_of_get? (w : World TT) (K : HKey) (c : K.1.Cell TT) (h : w.heap.get? K = some c) :
    w = { w with heap := w.heap.insert K c } := by
  have h' := World.eq_insert_getD w K c (by simp [h])
  rw [h, Option.getD_some] at h'
  exact h'

/-- A write shadowed by a later write to the same cell (with another cell written in between)
disappears. -/
theorem heap_insert_shadow (h : Heap TT) {k k' : HKind} {a a' : Nat} (c₁ c₃ : k.Cell TT) (c₂ : k'.Cell TT)
    (hne : (k, a) ≠ (k', a')) :
    ((h.insert (k, a) c₁).insert (k', a') c₂).insert (k, a) c₃ = (h.insert (k, a) c₃).insert (k', a') c₂ := by
  apply Std.ExtDHashMap.ext_get?
  intro key
  rw [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert]
  by_cases h1 : ((k, a) == key) = true
  · have e1 : (k, a) = key := by simpa using h1
    subst e1
    have h2 : ((k', a') == (k, a)) = false := by simpa using Ne.symm hne
    simp [h2]
  · by_cases h2 : ((k', a') == key) = true
    · simp [h1, h2]
    · simp [h1, h2]

theorem heap_insert_shadow_addr (h : Heap TT) (k k' : HKind) {a a' : Nat} (c₁ c₃ : k.Cell TT) (c₂ : k'.Cell TT)
    (ha : a ≠ a') :
    ((h.insert (k, a) c₁).insert (k', a') c₂).insert (k, a) c₃ = (h.insert (k, a) c₃).insert (k', a') c₂ :=
  heap_insert_shadow h c₁ c₃ c₂ (by intro e; exact ha (Prod.mk.inj e).2)

theorem heap_insert_shadow_kind (h : Heap TT) {k k' : HKind} (a a' : Nat) (c₁ c₃ : k.Cell TT) (c₂ : k'.Cell TT)
    (hk : k ≠ k') :
    ((h.insert (k, a) c₁).insert (k', a') c₂).insert (k, a) c₃ = (h.insert (k, a) c₃).insert (k', a') c₂ :=
  heap_insert_shadow h c₁ c₃ c₂ (by intro e; exact hk (Prod.mk.inj e).1)

/-- Two cells that exist can be written with their own contents. -/
theorem World.eq_insert2_getD (w : World TT) (K₁ K₂ : HKey) (d₁ : K₁.1.Cell TT) (d₂ : K₂.1.Cell TT)
    (h₁ : (w.heap.get? K₁).isSome = true) (h₂ : (w.heap.get? K₂).isSome = true) :
    w = { w with heap := (w.heap.insert K₁ ((w.heap.get? K₁).getD d₁)).insert K₂ ((w.heap.get? K₂).getD d₂) } := by
  have e1 := World.eq_insert_getD w K₁ d₁ h₁
  have e2 := World.eq_insert_getD w K₂ d₂ h₂
  have : (w.heap.insert K₁ ((w.heap.get? K₁).getD d₁)).insert K₂ ((w.heap.get? K₂).getD d₂) = w.heap := by
    have hh1 : w.heap.insert K₁ ((w.heap.get? K₁).getD d₁) = w.heap := by
      have := congrArg World.heap e1; exact this.symm
    have hh2 : w.heap.insert K₂ ((w.heap.get? K₂).getD d₂) = w.heap := by
      have := congrArg World.heap e2; exact this.symm
    rw [hh1, hh2]
  rw [this]

/-- Content of a cell known to exist, named without a case split. -/
def HKind.dflt : (k : HKind) → k.Cell TT
  | .arr _ => #[]
  | .tarr _ => #[]
  | .map _ _ => {}
  | .set _ => {}
  | .obj _ fs => OVals.empty fs
  | .promise _ => {}
  | .box _ => none
  | .dict _ => {}

theorem cell_some {α : Type} {o : Option α} (d : α) (h : o.isSome = true) : o = some (o.getD d) := by
  cases o <;> simp_all

/-- The Boolean of a merged condition (`if c then a else b` on booleans) is the merged Boolean,
so tests built from `&&`/`||` become propositions. -/
@[simp] theorem Val.toBool_ite (c : Prop) [Decidable c] (a b : Val TT .bool) :
    (if c then a else b).toBool = if c then a.toBool else b.toBool := by
  split <;> rfl

/-! ### Counted loops

`for (let i = k0; i < n; i++) body` with `n` fixed during the loop (a constant, or the length of
an array the body does not resize): the counter holds `ofNat k`, the condition evaluates to
`(ofNat k).lt (ofNat n)` and the step to `ofNat (k + 1)`. The loop is the fold of the body's
effect over the positions `k0 … n-1`, as elements of `Fin n` (so the body may index an array
of size `n` at the counter), and the counter ends at `ofNat n`. -/

/-- The positions from `k` on, as elements of `Fin n`. -/
theorem finRange_drop_eq_cons {n k : Nat} (hk : k < n) :
    (List.finRange n).drop k = ⟨k, hk⟩ :: (List.finRange n).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  simp

theorem evalLoop_count_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : Nat → σ → Env TT Γ) (put : κ → World TT)
    (n : Nat) (hn : n ≤ 2 ^ 53) (k0 : Nat) (hk0n : k0 ≤ 2 ^ 53)
    (C : Fin n → σ → κ → Completion TT ρ) (G : Fin n → σ → κ → σ) (H : Fin n → σ → κ → κ)
    (hcond : ∀ k s c, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) (put c) = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), put c))
    (hF : ∀ (i : Fin n) s c, exec (evalB I P body (enc i s)) (put c) =
      some (.ok (C i s c, enc i (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNext = true)
    (hstep : ∀ (i : Fin n) s c, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) (put c) = some (.ok (.normal, enc (i + 1) s), put c)) :
    ∀ (m k : Nat) (s : σ) (c : κ), n - k = m → k0 ≤ k → k ≤ max k0 n →
      exec (evalLoop I P cond body step (enc k s)) (put c) =
        some (.ok (.normal, enc (max k n)
            (((List.finRange n).drop k).foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s, c)).1),
          put (((List.finRange n).drop k).foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s, c)).2) := by
  intro m
  induction m with
  | zero =>
    intro k s c hm hk0k hk
    have hnk : n ≤ k := by omega
    have hlt : ¬ k < n := by omega
    rw [evalLoop.eq_1]
    have hd : (List.finRange n).drop k = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp only [exec_bind, exec_catchThrown, hcond k s c hk0k hk, lt_ofNat (a := k) (b := n) (by omega) hn,
      hlt, decide_false, Bool.false_eq_true, ite_false, exec_pure, hd, List.foldl_nil, Nat.max_eq_left hnk]
  | succ m ih =>
    intro k s c hm hk0k hk
    have hlt : k < n := by omega
    rw [Nat.max_eq_right (Nat.le_of_lt hlt)]
    rw [evalLoop.eq_1]
    simp only [exec_bind, exec_catchThrown, hcond k s c hk0k hk, lt_ofNat (a := k) (b := n) (by omega) hn, hlt,
      decide_true, ite_true]
    have hF' := hF ⟨k, hlt⟩ s c
    have hs' := hstep ⟨k, hlt⟩ (G ⟨k, hlt⟩ s c) (H ⟨k, hlt⟩ s c) (by simp only; omega)
    simp only at hF' hs'
    rw [hF']
    rw [finRange_drop_eq_cons hlt, List.foldl_cons]
    have ih' := ih (k + 1) (G ⟨k, hlt⟩ s c) (H ⟨k, hlt⟩ s c) (by omega) (by omega) (by omega)
    rw [Nat.max_eq_right (show k + 1 ≤ n by omega)] at ih'
    rcases Completion.eq_of_isNext (hC ⟨k, hlt⟩ s c) with h | h <;> rw [h] <;> simp only [exec_bind] <;>
      rw [hs'] <;> simp only [] <;> exact ih'

/-- **Counted loop, world unchanged.** If the condition is `i < n` on a counter holding
`ofNat k`, the step increments the counter, and one iteration of the body at position `i`
completes normally with new values `G i s` of the other mutable slots and the world as it
was, the loop is the left fold of `G` over the positions `k0 … n-1`. -/
theorem evalLoop_count_pure (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ : Type} (enc : Nat → σ → Env TT Γ) (n : Nat) (hn : n ≤ 2 ^ 53)
    (C : Fin n → σ → Completion TT ρ) (G : Fin n → σ → σ) (k0 : Nat) (s0 : σ)
    (env : Env TT Γ) (henv : env = enc k0 s0) (hk0 : k0 ≤ 2 ^ 53) (w : World TT)
    (hcond : ∀ k s, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) w = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), w))
    (hF : ∀ (i : Fin n) s, exec (evalB I P body (enc i s)) w = some (.ok (C i s, enc i (G i s)), w))
    (hC : ∀ i s, (C i s).isNext = true)
    (hstep : ∀ (i : Fin n) s, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) w = some (.ok (.normal, enc (i + 1) s), w)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (.normal, enc (max k0 n) (((List.finRange n).drop k0).foldl (fun s i => G i s) s0)), w) := by
  subst henv
  have h := evalLoop_count_aux I P cond body step enc (fun (_ : Unit) => w) n hn k0 hk0 (fun i s _ => C i s)
    (fun i s _ => G i s) (fun _ _ c => c) (fun k s _ hk0' hk => hcond k s hk0' hk) (fun i s _ => hF i s)
    (fun i s _ => hC i s) (fun i s _ h => hstep i s h) (n - k0) k0 s0 () rfl (Nat.le_refl k0) (Nat.le_max_left k0 n)
  simpa only [foldl_pair_const] using h

/-- **Counted loop, cells written** (as `evalForOf_summary_cells`). -/
theorem evalLoop_count_cells (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : Nat → σ → Env TT Γ) (put : κ → World TT)
    (n : Nat) (hn : n ≤ 2 ^ 53)
    (C : Fin n → σ → κ → Completion TT ρ) (G : Fin n → σ → κ → σ) (H : Fin n → σ → κ → κ)
    (k0 : Nat) (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc k0 s0) (hk0 : k0 ≤ 2 ^ 53)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k s c, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) (put c) = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), put c))
    (hF : ∀ (i : Fin n) s c, exec (evalB I P body (enc i s)) (put c) =
      some (.ok (C i s c, enc i (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNext = true)
    (hstep : ∀ (i : Fin n) s c, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) (put c) = some (.ok (.normal, enc (i + 1) s), put c)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (.normal, enc (max k0 n) (((List.finRange n).drop k0).foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s0, c0)).1),
        put (((List.finRange n).drop k0).foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s0, c0)).2) := by
  subst henv hw0
  exact evalLoop_count_aux I P cond body step enc put n hn k0 hk0 C G H hcond hF hC hstep (n - k0) k0 s0 c0 rfl (Nat.le_refl k0) (Nat.le_max_left k0 n)

/-- The size of an array state of fixed size (`evalLoop_count_sized`). -/
@[simp] theorem sized_size {t : Ty} {m : Nat} (c : {c : Array (Val TT t) // c.size = m}) : c.1.size = m := c.2

/-- **Counted loop over an array whose size the body keeps** (in-place updates `xs[j] = …`,
swaps; with the array `a` as the cell written). The cell's content is a state of fixed size `m0`
(`{c // c.size = m0}`), so a bound `xs.length` that the condition reads on every iteration is
the fixed `m0`; the body's new content `H i s c` comes with the obligation `hH` that it keeps the
size. -/
theorem evalLoop_count_sized (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ : Type} {t : Ty} (enc : Nat → σ → Env TT Γ) (w : World TT) (a : Nat)
    (m0 : Nat) (n : Nat) (hn : n ≤ 2 ^ 53)
    (C : Fin n → σ → {c : Array (Val TT t) // c.size = m0} → Completion TT ρ)
    (G : Fin n → σ → {c : Array (Val TT t) // c.size = m0} → σ)
    (H : Fin n → σ → {c : Array (Val TT t) // c.size = m0} → Array (Val TT t))
    (hH : ∀ i s c, (H i s c).size = m0)
    (k0 : Nat) (s0 : σ) (c0 : Array (Val TT t)) (hc0 : c0.size = m0) (env : Env TT Γ) (henv : env = enc k0 s0)
    (hk0 : k0 ≤ 2 ^ 53) (w0 : World TT) (hw0 : w0 = { w with heap := w.heap.insert (.arr t, a) c0 })
    (hcond : ∀ k s (c : {c : Array (Val TT t) // c.size = m0}), k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) { w with heap := w.heap.insert (.arr t, a) c.1 } =
        some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), { w with heap := w.heap.insert (.arr t, a) c.1 }))
    (hF : ∀ (i : Fin n) s (c : {c : Array (Val TT t) // c.size = m0}),
      exec (evalB I P body (enc i s)) { w with heap := w.heap.insert (.arr t, a) c.1 } =
        some (.ok (C i s c, enc i (G i s c)), { w with heap := w.heap.insert (.arr t, a) (H i s c) }))
    (hC : ∀ i s c, (C i s c).isNext = true)
    (hstep : ∀ (i : Fin n) s (c : {c : Array (Val TT t) // c.size = m0}), (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) { w with heap := w.heap.insert (.arr t, a) c.1 } =
        some (.ok (.normal, enc (i + 1) s), { w with heap := w.heap.insert (.arr t, a) c.1 })) :
    exec (evalLoop I P cond body step env) w0 =
      some (.ok (.normal, enc (max k0 n) (((List.finRange n).drop k0).foldl
          (fun p i => (G i p.1 p.2, (⟨H i p.1 p.2, hH i p.1 p.2⟩ : {c : Array (Val TT t) // c.size = m0})))
          (s0, ⟨c0, hc0⟩)).1),
        { w with heap := w.heap.insert (.arr t, a) (((List.finRange n).drop k0).foldl
          (fun p i => (G i p.1 p.2, (⟨H i p.1 p.2, hH i p.1 p.2⟩ : {c : Array (Val TT t) // c.size = m0})))
          (s0, ⟨c0, hc0⟩)).2.1 }) :=
  evalLoop_count_cells I P cond body step enc (fun c => { w with heap := w.heap.insert (.arr t, a) c.1 }) n hn
    C G (fun i s c => ⟨H i s c, hH i s c⟩) k0 s0 ⟨c0, hc0⟩ env henv hk0 w0 hw0 hcond hF hC hstep

/-- The value an iteration at position `i` returns, with the position: the counter of a counted
loop stays at `i` when the body returns. -/
def Completion.retAt? {ρ : Ty} (c : Completion TT ρ) (i : Nat) : Option (Val TT ρ × Nat) :=
  c.retVal?.map (·, i)

@[simp] theorem Completion.retAt?_normal {ρ : Ty} (i : Nat) : (Completion.normal : Completion TT ρ).retAt? i = none := rfl
@[simp] theorem Completion.retAt?_cont0 {ρ : Ty} (i : Nat) : (Completion.cont 0 : Completion TT ρ).retAt? i = none := rfl
@[simp] theorem Completion.retAt?_ret {ρ : Ty} (v : Val TT ρ) (i : Nat) : (Completion.ret v).retAt? i = some (v, i) := rfl
@[simp] theorem Completion.retAt?_ite {ρ : Ty} (c : Prop) [Decidable c] (a b : Completion TT ρ) (i : Nat) :
    (if c then a else b).retAt? i = (if c then a.retAt? i else b.retAt? i) := by
  split <;> rfl

/-- **Counted loop with `return`**: the fold over the positions carries the returned value and
the position where the loop stopped (the counter's final value, `n` when no iteration returned). -/
theorem evalLoop_count_ret_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : Nat → σ → Env TT Γ) (put : κ → World TT)
    (n : Nat) (hn : n ≤ 2 ^ 53) (k0 : Nat) (hk0n : k0 ≤ 2 ^ 53)
    (C : Fin n → σ → κ → Completion TT ρ) (G : Fin n → σ → κ → σ) (H : Fin n → σ → κ → κ)
    (hcond : ∀ k s c, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) (put c) = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), put c))
    (hF : ∀ (i : Fin n) s c, exec (evalB I P body (enc i s)) (put c) =
      some (.ok (C i s c, enc i (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNextOrRet = true)
    (hstep : ∀ (i : Fin n) s c, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) (put c) = some (.ok (.normal, enc (i + 1) s), put c)) :
    ∀ (m k : Nat) (s : σ) (c : κ), n - k = m → k0 ≤ k → k ≤ max k0 n →
      exec (evalLoop I P cond body step (enc k s)) (put c) =
        some (.ok (Completion.ofRet ((((List.finRange n).drop k).foldl
              (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s, c)).1.map Prod.fst),
            enc (((((List.finRange n).drop k).foldl
              (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s, c)).1.map Prod.snd).getD (max k n))
              (((List.finRange n).drop k).foldl (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s, c)).2.1),
          put (((List.finRange n).drop k).foldl (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s, c)).2.2) := by
  intro m
  induction m with
  | zero =>
    intro k s c hm hk0k hk
    have hnk : n ≤ k := by omega
    have hlt : ¬ k < n := by omega
    rw [evalLoop.eq_1]
    have hd : (List.finRange n).drop k = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp only [exec_bind, exec_catchThrown, hcond k s c hk0k hk, lt_ofNat (a := k) (b := n) (by omega) hn,
      hlt, decide_false, Bool.false_eq_true, ite_false, exec_pure, hd, List.foldl_nil, Nat.max_eq_left hnk,
      Option.map_none, Option.getD_none, Completion.ofRet_none]
  | succ m ih =>
    intro k s c hm hk0k hk
    have hlt : k < n := by omega
    rw [Nat.max_eq_right (Nat.le_of_lt hlt)]
    rw [evalLoop.eq_1]
    simp only [exec_bind, exec_catchThrown, hcond k s c hk0k hk, lt_ofNat (a := k) (b := n) (by omega) hn, hlt,
      decide_true, ite_true]
    have hF' := hF ⟨k, hlt⟩ s c
    simp only at hF'
    rw [hF']
    rw [finRange_drop_eq_cons hlt, List.foldl_cons]
    rcases Completion.cases_of_isNextOrRet (hC ⟨k, hlt⟩ s c) with h | h | ⟨v, h⟩
    all_goals rw [h]
    rotate_left 2
    · simp [retStep, h, foldl_retStep_done]
    all_goals
      have hs' := hstep ⟨k, hlt⟩ (G ⟨k, hlt⟩ s c) (H ⟨k, hlt⟩ s c) (by simp only; omega)
      simp only at hs'
      have hr : retStep (fun i s c => (C i s c).retAt? i.val) G H (none, s, c) ⟨k, hlt⟩ =
          (none, G ⟨k, hlt⟩ s c, H ⟨k, hlt⟩ s c) := by
        simp [retStep, h]
      simp only [exec_bind]
      rw [hs', hr]
      have ih' := ih (k + 1) (G ⟨k, hlt⟩ s c) (H ⟨k, hlt⟩ s c) (by omega) (by omega) (by omega)
      rw [Nat.max_eq_right (show k + 1 ≤ n by omega)] at ih'
      exact ih'

/-- **Counted loop with `return`, world unchanged.** -/
theorem evalLoop_count_pure_ret (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ : Type} (enc : Nat → σ → Env TT Γ) (n : Nat) (hn : n ≤ 2 ^ 53)
    (C : Fin n → σ → Completion TT ρ) (G : Fin n → σ → σ) (k0 : Nat) (s0 : σ)
    (env : Env TT Γ) (henv : env = enc k0 s0) (hk0 : k0 ≤ 2 ^ 53) (w : World TT)
    (hcond : ∀ k s, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) w = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), w))
    (hF : ∀ (i : Fin n) s, exec (evalB I P body (enc i s)) w = some (.ok (C i s, enc i (G i s)), w))
    (hC : ∀ i s, (C i s).isNextOrRet = true)
    (hstep : ∀ (i : Fin n) s, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) w = some (.ok (.normal, enc (i + 1) s), w)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (Completion.ofRet ((((List.finRange n).drop k0).foldl
            (retStep (fun i s (_ : Unit) => (C i s).retAt? i.val) (fun i s _ => G i s) (fun _ _ _ => ()))
            (none, s0, ())).1.map Prod.fst),
          enc (((((List.finRange n).drop k0).foldl
            (retStep (fun i s (_ : Unit) => (C i s).retAt? i.val) (fun i s _ => G i s) (fun _ _ _ => ()))
            (none, s0, ())).1.map Prod.snd).getD (max k0 n))
            (((List.finRange n).drop k0).foldl
              (retStep (fun i s (_ : Unit) => (C i s).retAt? i.val) (fun i s _ => G i s) (fun _ _ _ => ()))
              (none, s0, ())).2.1), w) := by
  subst henv
  exact evalLoop_count_ret_aux I P cond body step enc (fun (_ : Unit) => w) n hn k0 hk0 (fun i s _ => C i s)
    (fun i s _ => G i s) (fun _ _ _ => ()) (fun k s _ hk0' hk => hcond k s hk0' hk) (fun i s _ => hF i s)
    (fun i s _ => hC i s) (fun i s _ h => hstep i s h) (n - k0) k0 s0 () rfl (Nat.le_refl k0) (Nat.le_max_left k0 n)

/-- **Counted loop with `return`, cells written.** -/
theorem evalLoop_count_cells_ret (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : Nat → σ → Env TT Γ) (put : κ → World TT)
    (n : Nat) (hn : n ≤ 2 ^ 53)
    (C : Fin n → σ → κ → Completion TT ρ) (G : Fin n → σ → κ → σ) (H : Fin n → σ → κ → κ)
    (k0 : Nat) (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc k0 s0) (hk0 : k0 ≤ 2 ^ 53)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k s c, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) (put c) = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), put c))
    (hF : ∀ (i : Fin n) s c, exec (evalB I P body (enc i s)) (put c) =
      some (.ok (C i s c, enc i (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNextOrRet = true)
    (hstep : ∀ (i : Fin n) s c, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) (put c) = some (.ok (.normal, enc (i + 1) s), put c)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (Completion.ofRet ((((List.finRange n).drop k0).foldl
            (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s0, c0)).1.map Prod.fst),
          enc (((((List.finRange n).drop k0).foldl
            (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s0, c0)).1.map Prod.snd).getD (max k0 n))
            (((List.finRange n).drop k0).foldl (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s0, c0)).2.1),
        put (((List.finRange n).drop k0).foldl (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s0, c0)).2.2) := by
  subst henv hw0
  exact evalLoop_count_ret_aux I P cond body step enc put n hn k0 hk0 C G H hcond hF hC hstep (n - k0) k0 s0 c0 rfl (Nat.le_refl k0) (Nat.le_max_left k0 n)

/-- The position of an iteration that ends with `break` (the counter of a counted loop stays
there). -/
def Completion.brkAt? {ρ : Ty} (c : Completion TT ρ) (i : Nat) : Option Nat :=
  if c.isBrk0 then some i else none

@[simp] theorem Completion.brkAt?_normal {ρ : Ty} (i : Nat) : (Completion.normal : Completion TT ρ).brkAt? i = none := rfl
@[simp] theorem Completion.brkAt?_cont0 {ρ : Ty} (i : Nat) : (Completion.cont 0 : Completion TT ρ).brkAt? i = none := rfl
@[simp] theorem Completion.brkAt?_brk0 {ρ : Ty} (i : Nat) : (Completion.brk 0 : Completion TT ρ).brkAt? i = some i := rfl
@[simp] theorem Completion.brkAt?_ite {ρ : Ty} (c : Prop) [Decidable c] (a b : Completion TT ρ) (i : Nat) :
    (if c then a else b).brkAt? i = (if c then a.brkAt? i else b.brkAt? i) := by
  split <;> rfl

/-- **Counted loop with `break`**: the fold over the positions carries the position where the
loop broke off (the counter's final value, `n` when no iteration broke off). -/
theorem evalLoop_count_brk_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : Nat → σ → Env TT Γ) (put : κ → World TT)
    (n : Nat) (hn : n ≤ 2 ^ 53) (k0 : Nat) (hk0n : k0 ≤ 2 ^ 53)
    (C : Fin n → σ → κ → Completion TT ρ) (G : Fin n → σ → κ → σ) (H : Fin n → σ → κ → κ)
    (hcond : ∀ k s c, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) (put c) = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), put c))
    (hF : ∀ (i : Fin n) s c, exec (evalB I P body (enc i s)) (put c) =
      some (.ok (C i s c, enc i (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNextOrBrk = true)
    (hstep : ∀ (i : Fin n) s c, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) (put c) = some (.ok (.normal, enc (i + 1) s), put c)) :
    ∀ (m k : Nat) (s : σ) (c : κ), n - k = m → k0 ≤ k → k ≤ max k0 n →
      exec (evalLoop I P cond body step (enc k s)) (put c) =
        some (.ok (.normal,
            enc ((((List.finRange n).drop k).foldl
              (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s, c)).1.getD (max k n))
              (((List.finRange n).drop k).foldl (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s, c)).2.1),
          put (((List.finRange n).drop k).foldl (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s, c)).2.2) := by
  intro m
  induction m with
  | zero =>
    intro k s c hm hk0k hk
    have hnk : n ≤ k := by omega
    have hlt : ¬ k < n := by omega
    rw [evalLoop.eq_1]
    have hd : (List.finRange n).drop k = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp only [exec_bind, exec_catchThrown, hcond k s c hk0k hk, lt_ofNat (a := k) (b := n) (by omega) hn,
      hlt, decide_false, Bool.false_eq_true, ite_false, exec_pure, hd, List.foldl_nil, Nat.max_eq_left hnk,
      Option.getD_none]
  | succ m ih =>
    intro k s c hm hk0k hk
    have hlt : k < n := by omega
    rw [Nat.max_eq_right (Nat.le_of_lt hlt)]
    rw [evalLoop.eq_1]
    simp only [exec_bind, exec_catchThrown, hcond k s c hk0k hk, lt_ofNat (a := k) (b := n) (by omega) hn, hlt,
      decide_true, ite_true]
    have hF' := hF ⟨k, hlt⟩ s c
    simp only at hF'
    rw [hF']
    rw [finRange_drop_eq_cons hlt, List.foldl_cons]
    rcases Completion.cases_of_isNextOrBrk (hC ⟨k, hlt⟩ s c) with h | h | h
    all_goals rw [h]
    rotate_left 2
    · simp [retStep, h, foldl_retStep_done]
    all_goals
      have hs' := hstep ⟨k, hlt⟩ (G ⟨k, hlt⟩ s c) (H ⟨k, hlt⟩ s c) (by simp only; omega)
      simp only at hs'
      have hr : retStep (fun i s c => (C i s c).brkAt? i.val) G H (none, s, c) ⟨k, hlt⟩ =
          (none, G ⟨k, hlt⟩ s c, H ⟨k, hlt⟩ s c) := by
        simp [retStep, h]
      simp only [exec_bind]
      rw [hs', hr]
      have ih' := ih (k + 1) (G ⟨k, hlt⟩ s c) (H ⟨k, hlt⟩ s c) (by omega) (by omega) (by omega)
      rw [Nat.max_eq_right (show k + 1 ≤ n by omega)] at ih'
      exact ih'

/-- **Counted loop with `break`, world unchanged.** -/
theorem evalLoop_count_pure_brk (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ : Type} (enc : Nat → σ → Env TT Γ) (n : Nat) (hn : n ≤ 2 ^ 53)
    (C : Fin n → σ → Completion TT ρ) (G : Fin n → σ → σ) (k0 : Nat) (s0 : σ)
    (env : Env TT Γ) (henv : env = enc k0 s0) (hk0 : k0 ≤ 2 ^ 53) (w : World TT)
    (hcond : ∀ k s, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) w = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), w))
    (hF : ∀ (i : Fin n) s, exec (evalB I P body (enc i s)) w = some (.ok (C i s, enc i (G i s)), w))
    (hC : ∀ i s, (C i s).isNextOrBrk = true)
    (hstep : ∀ (i : Fin n) s, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) w = some (.ok (.normal, enc (i + 1) s), w)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (.normal,
          enc ((((List.finRange n).drop k0).foldl
            (retStep (fun i s (_ : Unit) => (C i s).brkAt? i.val) (fun i s _ => G i s) (fun _ _ _ => ()))
            (none, s0, ())).1.getD (max k0 n))
            (((List.finRange n).drop k0).foldl
              (retStep (fun i s (_ : Unit) => (C i s).brkAt? i.val) (fun i s _ => G i s) (fun _ _ _ => ()))
              (none, s0, ())).2.1), w) := by
  subst henv
  exact evalLoop_count_brk_aux I P cond body step enc (fun (_ : Unit) => w) n hn k0 hk0 (fun i s _ => C i s)
    (fun i s _ => G i s) (fun _ _ _ => ()) (fun k s _ hk0' hk => hcond k s hk0' hk) (fun i s _ => hF i s)
    (fun i s _ => hC i s) (fun i s _ h => hstep i s h) (n - k0) k0 s0 () rfl (Nat.le_refl k0) (Nat.le_max_left k0 n)

/-- **Counted loop with `break`, cells written.** -/
theorem evalLoop_count_cells_brk (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : Nat → σ → Env TT Γ) (put : κ → World TT)
    (n : Nat) (hn : n ≤ 2 ^ 53)
    (C : Fin n → σ → κ → Completion TT ρ) (G : Fin n → σ → κ → σ) (H : Fin n → σ → κ → κ)
    (k0 : Nat) (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc k0 s0) (hk0 : k0 ≤ 2 ^ 53)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k s c, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) (put c) = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), put c))
    (hF : ∀ (i : Fin n) s c, exec (evalB I P body (enc i s)) (put c) =
      some (.ok (C i s c, enc i (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNextOrBrk = true)
    (hstep : ∀ (i : Fin n) s c, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i s)) (put c) = some (.ok (.normal, enc (i + 1) s), put c)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (.normal,
          enc ((((List.finRange n).drop k0).foldl
            (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s0, c0)).1.getD (max k0 n))
            (((List.finRange n).drop k0).foldl (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s0, c0)).2.1),
        put (((List.finRange n).drop k0).foldl (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s0, c0)).2.2) := by
  subst henv hw0
  exact evalLoop_count_brk_aux I P cond body step enc put n hn k0 hk0 C G H hcond hF hC hstep (n - k0) k0 s0 c0 rfl (Nat.le_refl k0) (Nat.le_max_left k0 n)

/-! Bounds of counted loops other than `i < n`: `i < a - c` (`xs.length - 1`) and `i <= e` are
`i < n'` for a natural `n'` (`ts_summarize` rewrites the condition with these). -/

theorem lt_ofNat_sub_ofNat_eq {k a c : Nat} (hk : k ≤ 2 ^ 53) (ha : a ≤ 2 ^ 53) (hc : c ≤ 2 ^ 53) :
    (F64.ofNat k).lt (F64.ofNat a - F64.ofNat c) = (F64.ofNat k).lt (F64.ofNat (a - c)) := by
  by_cases h : c ≤ a
  · rw [ofNat_sub_ofNat ha h]
  · rw [lt_ofNat hk (by omega)]
    simp only [F64.ofNat_eq_ofInt]
    rw [F64.sub_ofInt (by simp only [F64.Safe]; omega) (by simp only [F64.Safe]; omega)
        (by simp only [F64.Safe]; omega),
      F64.lt_ofInt (by simp only [F64.Safe]; omega) (by simp only [F64.Safe]; omega)]
    simp only [decide_eq_decide]
    omega

/-- `s[i]` at a position of the string (the side condition is left to `omega`: in a counted loop
over another string of the same length, from the validation's equation). -/
theorem JSStr.at?_natCast_of_lt {s : JSStr} {n : Nat} (h : n < s.length) :
    s.at? (n : Int) = some ⟨[s.units[n]'h]⟩ := by
  simp only [JSStr.at?, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
  rw [ite_eq_right (by omega), List.getElem?_eq_getElem h]
  rfl

/-- A start above the bound: the loop does not run, and the counter stays at the start. -/
theorem lt_ofNat_max_eq {k k0 n : Nat} (hk0 : k0 ≤ k) (hk : k ≤ 2 ^ 53) (hn : n ≤ 2 ^ 53) (hm : max k0 n ≤ 2 ^ 53) :
    (F64.ofNat k).lt (F64.ofNat n) = (F64.ofNat k).lt (F64.ofNat (max k0 n)) := by
  rw [lt_ofNat hk hn, lt_ofNat hk hm]
  simp only [decide_eq_decide]
  omega

/-- `i + 1` with the literal as the translator writes it. -/
theorem ofNat_add_lit_one {n : Nat} (h : n + 1 ≤ 2 ^ 53) : F64.ofNat n + (1 : F64) = F64.ofNat (n + 1) :=
  ofNat_add_one h

theorem le_ofNat_eq_lt_succ {k e : Nat} (hk : k ≤ 2 ^ 53) (he : e + 1 ≤ 2 ^ 53) :
    (F64.ofNat k).le (F64.ofNat e) = (F64.ofNat k).lt (F64.ofNat (e + 1)) := by
  rw [le_ofNat hk (by omega), lt_ofNat hk he]
  simp only [decide_eq_decide]
  omega

theorem le_ofNat_sub_ofNat_eq {k a c : Nat} (hk : k ≤ 2 ^ 53) (ha : a + 1 ≤ 2 ^ 53) (hc : c ≤ 2 ^ 53) :
    (F64.ofNat k).le (F64.ofNat a - F64.ofNat c) = (F64.ofNat k).lt (F64.ofNat (a + 1 - c)) := by
  rw [lt_ofNat hk (by omega)]
  simp only [F64.ofNat_eq_ofInt]
  rw [F64.sub_ofInt (by simp only [F64.Safe]; omega) (by simp only [F64.Safe]; omega)
      (by simp only [F64.Safe]; omega),
    F64.le_ofInt (by simp only [F64.Safe]; omega) (by simp only [F64.Safe]; omega)]
  simp only [decide_eq_decide]
  omega

theorem le_ofNat_sub_one_eq {k a : Nat} (hk : k ≤ 2 ^ 53) (ha : a + 1 ≤ 2 ^ 53) :
    (F64.ofNat k).le (F64.ofNat a - F64.ofNat 1) = (F64.ofNat k).lt (F64.ofNat a) := by
  rw [le_ofNat_sub_ofNat_eq hk (by omega) (by omega), Nat.add_sub_cancel]

theorem finRange_find?_map_val {α : Type} (p : α → Bool) : ∀ (n : Nat) (f : Fin n → α),
    ((List.finRange n).find? (fun i => p (f i))).map Fin.val = (List.ofFn f).findIdx? p
  | 0, f => by simp
  | n + 1, f => by
    rw [List.finRange_succ, List.ofFn_succ, List.find?_cons, List.findIdx?_cons]
    cases h : p (f 0)
    · have ih := finRange_find?_map_val p n (fun i => f i.succ)
      simp only [List.find?_map, Option.map_map, Bool.false_eq_true, ite_false] at ih ⊢
      rw [← ih]
      simp [Function.comp_def]
    · simp

/-- `findIdx?` as the first matching position (the form of a counted search loop's summary:
`for (let i = 0; i < xs.length; i++) if (p(xs[i])) return i;`). -/
@[ts_sym] theorem Array.findIdx?_eq_finRange {α : Type} (p : α → Bool) (xs : Array α) :
    xs.findIdx? p = ((List.finRange xs.size).find? (fun i => p xs[i])).map Fin.val := by
  rw [finRange_find?_map_val p xs.size (fun i => xs[i])]
  have : List.ofFn (fun i : Fin xs.size => xs[i]) = xs.toList := by
    apply List.ext_getElem <;> simp
  rw [this, StrictTS.Array.findIdx?_eq_toList]

/-- **Counted loop, one cell written, no other mutable variable**: the fold is over the cell's
content alone. -/
theorem evalLoop_count_cell1 (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {κ : Type} (enc : Nat → Unit → Env TT Γ) (put : κ → World TT)
    (n : Nat) (hn : n ≤ 2 ^ 53) (C : Fin n → κ → Completion TT ρ) (H : Fin n → κ → κ)
    (k0 : Nat) (c0 : κ) (env : Env TT Γ) (henv : env = enc k0 ()) (hk0 : k0 ≤ 2 ^ 53)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k c, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k ())) (put c) = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), put c))
    (hF : ∀ (i : Fin n) c, exec (evalB I P body (enc i ())) (put c) = some (.ok (C i c, enc i ()), put (H i c)))
    (hC : ∀ i c, (C i c).isNext = true)
    (hstep : ∀ (i : Fin n) c, (i : Nat) + 1 ≤ 2 ^ 53 →
      exec (evalB I P step (enc i ())) (put c) = some (.ok (.normal, enc (i + 1) ()), put c)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (.normal, enc (max k0 n) ()), put (((List.finRange n).drop k0).foldl (fun c i => H i c) c0)) := by
  subst henv hw0
  have h := evalLoop_count_aux I P cond body step enc put n hn k0 hk0 (fun i _ c => C i c) (fun _ _ _ => ())
    (fun i _ c => H i c) (fun k _ c hk0' hk => hcond k c hk0' hk) (fun i _ c => hF i c) (fun i _ c => hC i c)
    (fun i _ c h => hstep i c h) (n - k0) k0 () c0 rfl (Nat.le_refl k0) (Nat.le_max_left k0 n)
  simpa only [foldl_pair_unit] using h

/-! ### Starts that are not literals

`for (let i = Math.min(Math.floor(n), 50); i > 0; i--)`: when the condition fails at the start,
the loop does not run; when it holds, the start is `ofNat k` for the `k` it denotes
(`F64.floor_min_gt`), and the loop is a counted loop from there (`evalLoop_start_split`). -/

/-- A loop whose condition is false at the start does not run. -/
theorem evalLoop_false_start (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (env : Env TT Γ) (w : World TT)
    (hcond : exec (evalE I P cond env) w = some (.ok (.bool false), w)) :
    exec (evalLoop I P cond body step env) w = some (.ok (.normal, env), w) := by
  rw [evalLoop.eq_1]
  simp [exec_bind, exec_catchThrown, hcond]

/-- Split on a loop's condition at the start (`b`, its value): if it holds, go on with that fact
(`ts_summarize` then rewrites a computed start into `ofNat k`); if not, the loop runs no
iteration. -/
theorem evalLoop_split_start {Q : Prop} (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (cond : Expr TT Γ .bool) (body step : Block TT Γ ρ) (env : Env TT Γ) (w : World TT) (b : Bool)
    (hcond : exec (evalE I P cond env) w = some (.ok (.bool b), w)) (hpos : b = true → Q)
    (hneg : b = false → exec (evalLoop I P cond body step env) w = some (.ok (.normal, env), w) → Q) :
    Q := by
  cases b with
  | true => exact hpos rfl
  | false => exact hneg rfl (evalLoop_false_start I P cond body step env w hcond)

/-! ### `while` loops that are counted loops

`while (i < n) { …; i++ }`: the counter step is the last statement of the body, so one
iteration of the body moves the counter from `k` to `k + 1` (a `continue` would skip the step:
the symbolic iteration then does not have that shape, and no summary is produced). -/

theorem evalLoop_while_up_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body : Block TT Γ ρ) {σ κ : Type} (enc : Nat → σ → Env TT Γ) (put : κ → World TT)
    (n : Nat) (hn : n ≤ 2 ^ 53) (k0 : Nat) (hk0n : k0 ≤ 2 ^ 53)
    (C : Fin n → σ → κ → Completion TT ρ) (G : Fin n → σ → κ → σ) (H : Fin n → σ → κ → κ)
    (hcond : ∀ k s c, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) (put c) = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), put c))
    (hF : ∀ (i : Fin n) s c, exec (evalB I P body (enc i s)) (put c) =
      some (.ok (C i s c, enc (i + 1) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNext = true) :
    ∀ (m k : Nat) (s : σ) (c : κ), n - k = m → k0 ≤ k → k ≤ max k0 n →
      exec (evalLoop I P cond body .nil (enc k s)) (put c) =
        some (.ok (.normal, enc (max k n)
            (((List.finRange n).drop k).foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s, c)).1),
          put (((List.finRange n).drop k).foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s, c)).2) := by
  intro m
  induction m with
  | zero =>
    intro k s c hm hk0k hk
    have hnk : n ≤ k := by omega
    have hlt : ¬ k < n := by omega
    rw [evalLoop.eq_1]
    have hd : (List.finRange n).drop k = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp only [exec_bind, exec_catchThrown, hcond k s c hk0k hk, lt_ofNat (a := k) (b := n) (by omega) hn,
      hlt, decide_false, Bool.false_eq_true, ite_false, exec_pure, hd, List.foldl_nil, Nat.max_eq_left hnk]
  | succ m ih =>
    intro k s c hm hk0k hk
    have hlt : k < n := by omega
    rw [Nat.max_eq_right (Nat.le_of_lt hlt)]
    rw [evalLoop.eq_1]
    simp only [exec_bind, exec_catchThrown, hcond k s c hk0k hk, lt_ofNat (a := k) (b := n) (by omega) hn, hlt,
      decide_true, ite_true]
    have hF' := hF ⟨k, hlt⟩ s c
    simp only at hF'
    rw [hF']
    rw [finRange_drop_eq_cons hlt, List.foldl_cons]
    have ih' := ih (k + 1) (G ⟨k, hlt⟩ s c) (H ⟨k, hlt⟩ s c) (by omega) (by omega) (by omega)
    rw [Nat.max_eq_right (show k + 1 ≤ n by omega)] at ih'
    rcases Completion.eq_of_isNext (hC ⟨k, hlt⟩ s c) with h | h <;> rw [h] <;>
      simp only [exec_bind, evalB.eq_1, exec_pure] <;> exact ih'

/-- **`while (i < n) { …; i++ }`, cells written** (with `κ = Unit` for an unchanged world). -/
theorem evalLoop_while_up_cells (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body : Block TT Γ ρ) {σ κ : Type} (enc : Nat → σ → Env TT Γ) (put : κ → World TT)
    (n : Nat) (hn : n ≤ 2 ^ 53)
    (C : Fin n → σ → κ → Completion TT ρ) (G : Fin n → σ → κ → σ) (H : Fin n → σ → κ → κ)
    (k0 : Nat) (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc k0 s0) (hk0 : k0 ≤ 2 ^ 53)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k s c, k0 ≤ k → k ≤ max k0 n →
      exec (evalE I P cond (enc k s)) (put c) = some (.ok (.bool ((F64.ofNat k).lt (F64.ofNat n))), put c))
    (hF : ∀ (i : Fin n) s c, exec (evalB I P body (enc i s)) (put c) =
      some (.ok (C i s c, enc (i + 1) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNext = true) :
    exec (evalLoop I P cond body .nil env) w =
      some (.ok (.normal, enc (max k0 n) (((List.finRange n).drop k0).foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s0, c0)).1),
        put (((List.finRange n).drop k0).foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s0, c0)).2) := by
  subst henv hw0
  exact evalLoop_while_up_aux I P cond body enc put n hn k0 hk0 C G H hcond hF hC (n - k0) k0 s0 c0 rfl
    (Nat.le_refl k0) (Nat.le_max_left k0 n)

/-! ### Backwards counted loops `for (let i = x0; P(i); i--)`

The counter is a double: before the test at time `k` it holds `k - 1` (`F64.ofNat k - F64.ofNat 1`),
so the start `xs.length - 1` is time `xs.length`, and the exit `i >= 0` happens at time `0`
(the counter `-1`). The body at time `k > m` runs at the position `k - 1`. -/

theorem finRange_drop_take_succ {N m j : Nat} (h : m + j < N) :
    ((List.finRange N).drop m).take (j + 1) = ((List.finRange N).drop m).take j ++ [⟨m + j, h⟩] := by
  rw [List.take_add_one]
  congr 1
  rw [List.getElem?_drop, List.getElem?_eq_getElem (by simpa using h)]
  simp

theorem evalLoop_down_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNext = true)
    (hstep : ∀ (i : Fin N) s c, exec (evalB I P step (enc (F64.ofNat i) s)) (put c) =
      some (.ok (.normal, enc (F64.ofNat i - F64.ofNat 1) s), put c)) :
    ∀ (j k : Nat) (s : σ) (c : κ), k - m = j → m ≤ k → k ≤ N →
      exec (evalLoop I P cond body step (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) =
        some (.ok (.normal, enc (F64.ofNat m - F64.ofNat 1)
            ((((List.finRange N).drop m).take (k - m)).reverse.foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s, c)).1),
          put ((((List.finRange N).drop m).take (k - m)).reverse.foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s, c)).2) := by
  intro j
  induction j with
  | zero =>
    intro k s c hj hmk hkN
    obtain rfl : k = m := by omega
    rw [evalLoop.eq_1]
    simp [exec_bind, exec_catchThrown, hcond k s c hkN, hPm]
  | succ j ih =>
    intro k s c hj hmk hkN
    have hk1 : 1 ≤ k := by omega
    have hpos : m + j < N := by omega
    have hkj : k - 1 = m + j := by omega
    rw [evalLoop.eq_1]
    simp only [exec_bind, exec_catchThrown, hcond k s c hkN, hP k (by omega) hkN, ite_true]
    -- the counter `k - 1` is the position `m + j`
    have hctr : F64.ofNat k - F64.ofNat 1 = F64.ofNat (m + j) := by
      rw [ofNat_sub_ofNat (by omega) hk1, hkj]
    rw [hctr]
    have hF' := hF ⟨m + j, hpos⟩ s c
    have hs' := hstep ⟨m + j, hpos⟩ (G ⟨m + j, hpos⟩ s c) (H ⟨m + j, hpos⟩ s c)
    simp only at hF' hs'
    rw [hF']
    rw [show k - m = j + 1 by omega, finRange_drop_take_succ hpos, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons]
    have ih' := ih (m + j) (G ⟨m + j, hpos⟩ s c) (H ⟨m + j, hpos⟩ s c) (by omega) (by omega) (by omega)
    rw [show m + j - m = j by omega] at ih'
    rcases Completion.eq_of_isNext (hC ⟨m + j, hpos⟩ s c) with h | h <;> rw [h] <;> simp only [exec_bind] <;>
      rw [hs'] <;> simp only [] <;> exact ih'


theorem evalLoop_down_ret_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNextOrRet = true)
    (hstep : ∀ (i : Fin N) s c, exec (evalB I P step (enc (F64.ofNat i) s)) (put c) =
      some (.ok (.normal, enc (F64.ofNat i - F64.ofNat 1) s), put c)) :
    ∀ (j k : Nat) (s : σ) (c : κ), k - m = j → m ≤ k → k ≤ N →
      exec (evalLoop I P cond body step (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) =
        some (.ok (Completion.ofRet (((((List.finRange N).drop m).take (k - m)).reverse.foldl
              (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s, c)).1.map Prod.fst),
            enc ((((((List.finRange N).drop m).take (k - m)).reverse.foldl
              (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s, c)).1.map (fun p => F64.ofNat p.2)).getD
                (F64.ofNat m - F64.ofNat 1))
              ((((List.finRange N).drop m).take (k - m)).reverse.foldl
                (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s, c)).2.1),
          put ((((List.finRange N).drop m).take (k - m)).reverse.foldl
            (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s, c)).2.2) := by
  intro j
  induction j with
  | zero =>
    intro k s c hj hmk hkN
    obtain rfl : k = m := by omega
    rw [evalLoop.eq_1]
    simp [exec_bind, exec_catchThrown, hcond k s c hkN, hPm]
  | succ j ih =>
    intro k s c hj hmk hkN
    have hk1 : 1 ≤ k := by omega
    have hpos : m + j < N := by omega
    have hkj : k - 1 = m + j := by omega
    rw [evalLoop.eq_1]
    simp only [exec_bind, exec_catchThrown, hcond k s c hkN, hP k (by omega) hkN, ite_true]
    have hctr : F64.ofNat k - F64.ofNat 1 = F64.ofNat (m + j) := by
      rw [ofNat_sub_ofNat (by omega) hk1, hkj]
    rw [hctr]
    have hF' := hF ⟨m + j, hpos⟩ s c
    simp only at hF'
    rw [hF']
    rw [show k - m = j + 1 by omega, finRange_drop_take_succ hpos, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons]
    rcases Completion.cases_of_isNextOrRet (hC ⟨m + j, hpos⟩ s c) with h | h | ⟨v, h⟩
    all_goals rw [h]
    rotate_left 2
    · have hr : retStep (fun i s c => (C i s c).retAt? i.val) G H (none, s, c) ⟨m + j, hpos⟩ =
          (some (v, m + j), G ⟨m + j, hpos⟩ s c, H ⟨m + j, hpos⟩ s c) := by
        simp [retStep, h]
      rw [hr, foldl_retStep_done]
      simp
    all_goals
      have hs' := hstep ⟨m + j, hpos⟩ (G ⟨m + j, hpos⟩ s c) (H ⟨m + j, hpos⟩ s c)
      simp only at hs'
      have hr : retStep (fun i s c => (C i s c).retAt? i.val) G H (none, s, c) ⟨m + j, hpos⟩ =
          (none, G ⟨m + j, hpos⟩ s c, H ⟨m + j, hpos⟩ s c) := by
        simp [retStep, h]
      have ih' := ih (m + j) (G ⟨m + j, hpos⟩ s c) (H ⟨m + j, hpos⟩ s c) (by omega) (by omega) (by omega)
      rw [show m + j - m = j by omega] at ih'
      simp only [exec_bind]
      rw [hs', hr]
      exact ih'

theorem evalLoop_down_brk_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNextOrBrk = true)
    (hstep : ∀ (i : Fin N) s c, exec (evalB I P step (enc (F64.ofNat i) s)) (put c) =
      some (.ok (.normal, enc (F64.ofNat i - F64.ofNat 1) s), put c)) :
    ∀ (j k : Nat) (s : σ) (c : κ), k - m = j → m ≤ k → k ≤ N →
      exec (evalLoop I P cond body step (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) =
        some (.ok (.normal,
            enc ((((((List.finRange N).drop m).take (k - m)).reverse.foldl
              (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s, c)).1.map F64.ofNat).getD
                (F64.ofNat m - F64.ofNat 1))
              ((((List.finRange N).drop m).take (k - m)).reverse.foldl
                (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s, c)).2.1),
          put ((((List.finRange N).drop m).take (k - m)).reverse.foldl
            (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s, c)).2.2) := by
  intro j
  induction j with
  | zero =>
    intro k s c hj hmk hkN
    obtain rfl : k = m := by omega
    rw [evalLoop.eq_1]
    simp [exec_bind, exec_catchThrown, hcond k s c hkN, hPm]
  | succ j ih =>
    intro k s c hj hmk hkN
    have hk1 : 1 ≤ k := by omega
    have hpos : m + j < N := by omega
    have hkj : k - 1 = m + j := by omega
    rw [evalLoop.eq_1]
    simp only [exec_bind, exec_catchThrown, hcond k s c hkN, hP k (by omega) hkN, ite_true]
    have hctr : F64.ofNat k - F64.ofNat 1 = F64.ofNat (m + j) := by
      rw [ofNat_sub_ofNat (by omega) hk1, hkj]
    rw [hctr]
    have hF' := hF ⟨m + j, hpos⟩ s c
    simp only at hF'
    rw [hF']
    rw [show k - m = j + 1 by omega, finRange_drop_take_succ hpos, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons]
    rcases Completion.cases_of_isNextOrBrk (hC ⟨m + j, hpos⟩ s c) with h | h | h
    all_goals rw [h]
    rotate_left 2
    · have hr : retStep (fun i s c => (C i s c).brkAt? i.val) G H (none, s, c) ⟨m + j, hpos⟩ =
          (some (m + j), G ⟨m + j, hpos⟩ s c, H ⟨m + j, hpos⟩ s c) := by
        simp [retStep, h]
      rw [hr, foldl_retStep_done]
      simp
    all_goals
      have hs' := hstep ⟨m + j, hpos⟩ (G ⟨m + j, hpos⟩ s c) (H ⟨m + j, hpos⟩ s c)
      simp only at hs'
      have hr : retStep (fun i s c => (C i s c).brkAt? i.val) G H (none, s, c) ⟨m + j, hpos⟩ =
          (none, G ⟨m + j, hpos⟩ s c, H ⟨m + j, hpos⟩ s c) := by
        simp [retStep, h]
      have ih' := ih (m + j) (G ⟨m + j, hpos⟩ s c) (H ⟨m + j, hpos⟩ s c) (by omega) (by omega) (by omega)
      rw [show m + j - m = j by omega] at ih'
      simp only [exec_bind]
      rw [hs', hr]
      exact ih'

theorem take_finRange_drop_full (N m : Nat) :
    ((List.finRange N).drop m).take (N - m) = (List.finRange N).drop m :=
  List.take_of_length_le (by simp)

/-- **Backwards counted loop** `for (let i = x0; P(i); i--)` with `x0 = N - 1` as a double (`xs.length - 1`,
or a literal start `k0 = (k0 + 1) - 1`): the fold over the positions `N - 1` down to `m`, where the
condition at counter `k - 1` is true for `m < k ≤ N` and false at `k = m`; the counter ends at `m - 1`. -/
theorem evalLoop_down_cells (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (x0 : F64) (hx0 : x0 = F64.ofNat N - F64.ofNat 1) (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc x0 s0)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNext = true)
    (hstep : ∀ (i : Fin N) s c, exec (evalB I P step (enc (F64.ofNat i) s)) (put c) =
      some (.ok (.normal, enc (F64.ofNat i - F64.ofNat 1) s), put c)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (.normal, enc (F64.ofNat m - F64.ofNat 1)
          (((List.finRange N).drop m).reverse.foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s0, c0)).1),
        put (((List.finRange N).drop m).reverse.foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s0, c0)).2) := by
  subst henv hw0 hx0
  have h := evalLoop_down_aux I P cond body step enc put N m hN hmN Pc C G H hcond hP hPm hF hC hstep
    (N - m) N s0 c0 rfl hmN (Nat.le_refl N)
  rw [take_finRange_drop_full] at h
  exact h

/-- **Backwards counted loop with `return`.** -/
theorem evalLoop_down_cells_ret (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (x0 : F64) (hx0 : x0 = F64.ofNat N - F64.ofNat 1) (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc x0 s0)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNextOrRet = true)
    (hstep : ∀ (i : Fin N) s c, exec (evalB I P step (enc (F64.ofNat i) s)) (put c) =
      some (.ok (.normal, enc (F64.ofNat i - F64.ofNat 1) s), put c)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (Completion.ofRet ((((List.finRange N).drop m).reverse.foldl
            (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s0, c0)).1.map Prod.fst),
          enc (((((List.finRange N).drop m).reverse.foldl
            (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s0, c0)).1.map (fun p => F64.ofNat p.2)).getD
              (F64.ofNat m - F64.ofNat 1))
            (((List.finRange N).drop m).reverse.foldl
              (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s0, c0)).2.1),
        put (((List.finRange N).drop m).reverse.foldl
          (retStep (fun i s c => (C i s c).retAt? i.val) G H) (none, s0, c0)).2.2) := by
  subst henv hw0 hx0
  have h := evalLoop_down_ret_aux I P cond body step enc put N m hN hmN Pc C G H hcond hP hPm hF hC hstep
    (N - m) N s0 c0 rfl hmN (Nat.le_refl N)
  rw [take_finRange_drop_full] at h
  exact h

/-- **Backwards counted loop with `break`.** -/
theorem evalLoop_down_cells_brk (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (x0 : F64) (hx0 : x0 = F64.ofNat N - F64.ofNat 1) (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc x0 s0)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNextOrBrk = true)
    (hstep : ∀ (i : Fin N) s c, exec (evalB I P step (enc (F64.ofNat i) s)) (put c) =
      some (.ok (.normal, enc (F64.ofNat i - F64.ofNat 1) s), put c)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (.normal,
          enc (((((List.finRange N).drop m).reverse.foldl
            (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s0, c0)).1.map F64.ofNat).getD
              (F64.ofNat m - F64.ofNat 1))
            (((List.finRange N).drop m).reverse.foldl
              (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s0, c0)).2.1),
        put (((List.finRange N).drop m).reverse.foldl
          (retStep (fun i s c => (C i s c).brkAt? i.val) G H) (none, s0, c0)).2.2) := by
  subst henv hw0 hx0
  have h := evalLoop_down_brk_aux I P cond body step enc put N m hN hmN Pc C G H hcond hP hPm hF hC hstep
    (N - m) N s0 c0 rfl hmN (Nat.le_refl N)
  rw [take_finRange_drop_full] at h
  exact h

/-- `while (i >= c) { …; i-- }`: the body moves the counter from the position `i` to `i - 1`. -/
theorem evalLoop_down_while_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i - F64.ofNat 1) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNext = true) :
    ∀ (j k : Nat) (s : σ) (c : κ), k - m = j → m ≤ k → k ≤ N →
      exec (evalLoop I P cond body .nil (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) =
        some (.ok (.normal, enc (F64.ofNat m - F64.ofNat 1)
            ((((List.finRange N).drop m).take (k - m)).reverse.foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s, c)).1),
          put ((((List.finRange N).drop m).take (k - m)).reverse.foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s, c)).2) := by
  intro j
  induction j with
  | zero =>
    intro k s c hj hmk hkN
    obtain rfl : k = m := by omega
    rw [evalLoop.eq_1]
    simp [exec_bind, exec_catchThrown, hcond k s c hkN, hPm]
  | succ j ih =>
    intro k s c hj hmk hkN
    have hk1 : 1 ≤ k := by omega
    have hpos : m + j < N := by omega
    have hkj : k - 1 = m + j := by omega
    rw [evalLoop.eq_1]
    simp only [exec_bind, exec_catchThrown, hcond k s c hkN, hP k (by omega) hkN, ite_true]
    have hctr : F64.ofNat k - F64.ofNat 1 = F64.ofNat (m + j) := by
      rw [ofNat_sub_ofNat (by omega) hk1, hkj]
    rw [hctr]
    have hF' := hF ⟨m + j, hpos⟩ s c
    simp only at hF'
    rw [hF']
    rw [show k - m = j + 1 by omega, finRange_drop_take_succ hpos, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons]
    have ih' := ih (m + j) (G ⟨m + j, hpos⟩ s c) (H ⟨m + j, hpos⟩ s c) (by omega) (by omega) (by omega)
    rw [show m + j - m = j by omega] at ih'
    rcases Completion.eq_of_isNext (hC ⟨m + j, hpos⟩ s c) with h | h <;> rw [h] <;>
      simp only [exec_bind, evalB.eq_1, exec_pure] <;> exact ih'

/-- **`while (i >= c) { …; i-- }` (or `i > c`), cells written**, from `x0 = N - 1`. -/
theorem evalLoop_down_while_cells (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (x0 : F64) (hx0 : x0 = F64.ofNat N - F64.ofNat 1) (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc x0 s0)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i - F64.ofNat 1) (G i s c)), put (H i s c)))
    (hC : ∀ i s c, (C i s c).isNext = true) :
    exec (evalLoop I P cond body .nil env) w =
      some (.ok (.normal, enc (F64.ofNat m - F64.ofNat 1)
          (((List.finRange N).drop m).reverse.foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s0, c0)).1),
        put (((List.finRange N).drop m).reverse.foldl (fun p i => (G i p.1 p.2, H i p.1 p.2)) (s0, c0)).2) := by
  subst henv hw0 hx0
  have h := evalLoop_down_while_aux I P cond body enc put N m hN hmN Pc C G H hcond hP hPm hF hC
    (N - m) N s0 c0 rfl hmN (Nat.le_refl N)
  rw [take_finRange_drop_full] at h
  exact h

/-- The value an iteration returns, with its position and the world after it. -/
def Completion.retAtW? {ρ : Ty} (c : Completion TT ρ) (i : Nat) (w : World TT) : Option (Val TT ρ × Nat × World TT) :=
  c.retVal?.map (·, i, w)

@[simp] theorem Completion.retAtW?_normal {ρ : Ty} (i : Nat) (w : World TT) :
    (Completion.normal : Completion TT ρ).retAtW? i w = none := rfl
@[simp] theorem Completion.retAtW?_cont0 {ρ : Ty} (i : Nat) (w : World TT) :
    (Completion.cont 0 : Completion TT ρ).retAtW? i w = none := rfl
@[simp] theorem Completion.retAtW?_ret {ρ : Ty} (v : Val TT ρ) (i : Nat) (w : World TT) :
    (Completion.ret v).retAtW? i w = some (v, i, w) := rfl
@[simp] theorem Completion.retAtW?_ite {ρ : Ty} (c : Prop) [Decidable c] (a b : Completion TT ρ) (i : Nat)
    (w : World TT) : (if c then a else b).retAtW? i w = (if c then a.retAtW? i w else b.retAtW? i w) := by
  split <;> rfl

theorem evalLoop_down_retw_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (W : Fin N → σ → κ → World TT)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i) (G i s c)), W i s c))
    (hW : ∀ i s c, (C i s c).isNext = true → W i s c = put (H i s c))
    (hC : ∀ i s c, (C i s c).isNextOrRet = true)
    (hstep : ∀ (i : Fin N) s c, exec (evalB I P step (enc (F64.ofNat i) s)) (put c) =
      some (.ok (.normal, enc (F64.ofNat i - F64.ofNat 1) s), put c)) :
    ∀ (j k : Nat) (s : σ) (c : κ), k - m = j → m ≤ k → k ≤ N →
      exec (evalLoop I P cond body step (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) =
        some (.ok (Completion.ofRet (((((List.finRange N).drop m).take (k - m)).reverse.foldl
              (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s, c)).1.map Prod.fst),
            enc ((((((List.finRange N).drop m).take (k - m)).reverse.foldl
              (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s, c)).1.map
                (fun p => F64.ofNat p.2.1)).getD (F64.ofNat m - F64.ofNat 1))
              ((((List.finRange N).drop m).take (k - m)).reverse.foldl
                (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s, c)).2.1),
          ((((((List.finRange N).drop m).take (k - m)).reverse.foldl
            (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s, c)).1.map
              (fun p => p.2.2)).getD
            (put ((((List.finRange N).drop m).take (k - m)).reverse.foldl
              (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s, c)).2.2))) := by
  intro j
  induction j with
  | zero =>
    intro k s c hj hmk hkN
    obtain rfl : k = m := by omega
    rw [evalLoop.eq_1]
    simp [exec_bind, exec_catchThrown, hcond k s c hkN, hPm]
  | succ j ih =>
    intro k s c hj hmk hkN
    have hk1 : 1 ≤ k := by omega
    have hpos : m + j < N := by omega
    have hkj : k - 1 = m + j := by omega
    rw [evalLoop.eq_1]
    simp only [exec_bind, exec_catchThrown, hcond k s c hkN, hP k (by omega) hkN, ite_true]
    have hctr : F64.ofNat k - F64.ofNat 1 = F64.ofNat (m + j) := by
      rw [ofNat_sub_ofNat (by omega) hk1, hkj]
    rw [hctr]
    have hF' := hF ⟨m + j, hpos⟩ s c
    simp only at hF'
    rw [hF']
    rw [show k - m = j + 1 by omega, finRange_drop_take_succ hpos, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons]
    rcases Completion.cases_of_isNextOrRet (hC ⟨m + j, hpos⟩ s c) with h | h | ⟨v, h⟩
    rotate_left 2
    · rw [h]
      have hr : retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H (none, s, c) ⟨m + j, hpos⟩ =
          (some (v, m + j, W ⟨m + j, hpos⟩ s c), G ⟨m + j, hpos⟩ s c, H ⟨m + j, hpos⟩ s c) := by
        simp [retStep, h]
      rw [hr, foldl_retStep_done]
      simp
    all_goals
      have hw := hW ⟨m + j, hpos⟩ s c (by rw [h]; rfl)
      rw [hw, h]
      have hs' := hstep ⟨m + j, hpos⟩ (G ⟨m + j, hpos⟩ s c) (H ⟨m + j, hpos⟩ s c)
      simp only at hs'
      have hr : retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H (none, s, c) ⟨m + j, hpos⟩ =
          (none, G ⟨m + j, hpos⟩ s c, H ⟨m + j, hpos⟩ s c) := by
        simp [retStep, h]
      have ih' := ih (m + j) (G ⟨m + j, hpos⟩ s c) (H ⟨m + j, hpos⟩ s c) (by omega) (by omega) (by omega)
      rw [show m + j - m = j by omega] at ih'
      simp only [exec_bind]
      rw [hs', hr]
      exact ih'

/-- **Backwards counted loop with `return`, the returning iteration changing the world freely**
(`return xs.slice(0, i + 1)` allocates): the fold also keeps the world after the returning
iteration, which is the loop's world when it returned. -/
theorem evalLoop_down_cells_retw (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cond : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) {σ κ : Type} (enc : F64 → σ → Env TT Γ) (put : κ → World TT)
    (N m : Nat) (hN : N ≤ 2 ^ 53) (hmN : m ≤ N) (Pc : Nat → Bool)
    (C : Fin N → σ → κ → Completion TT ρ) (G : Fin N → σ → κ → σ) (H : Fin N → σ → κ → κ)
    (W : Fin N → σ → κ → World TT)
    (x0 : F64) (hx0 : x0 = F64.ofNat N - F64.ofNat 1) (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc x0 s0)
    (w : World TT) (hw0 : w = put c0)
    (hcond : ∀ k s c, k ≤ N →
      exec (evalE I P cond (enc (F64.ofNat k - F64.ofNat 1) s)) (put c) = some (.ok (.bool (Pc k)), put c))
    (hP : ∀ k, m < k → k ≤ N → Pc k = true) (hPm : Pc m = false)
    (hF : ∀ (i : Fin N) s c, exec (evalB I P body (enc (F64.ofNat i) s)) (put c) =
      some (.ok (C i s c, enc (F64.ofNat i) (G i s c)), W i s c))
    (hW : ∀ i s c, (C i s c).isNext = true → W i s c = put (H i s c))
    (hC : ∀ i s c, (C i s c).isNextOrRet = true)
    (hstep : ∀ (i : Fin N) s c, exec (evalB I P step (enc (F64.ofNat i) s)) (put c) =
      some (.ok (.normal, enc (F64.ofNat i - F64.ofNat 1) s), put c)) :
    exec (evalLoop I P cond body step env) w =
      some (.ok (Completion.ofRet ((((List.finRange N).drop m).reverse.foldl
            (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s0, c0)).1.map Prod.fst),
          enc (((((List.finRange N).drop m).reverse.foldl
            (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s0, c0)).1.map
              (fun p => F64.ofNat p.2.1)).getD (F64.ofNat m - F64.ofNat 1))
            (((List.finRange N).drop m).reverse.foldl
              (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s0, c0)).2.1),
        (((((List.finRange N).drop m).reverse.foldl
          (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s0, c0)).1.map (fun p => p.2.2)).getD
          (put (((List.finRange N).drop m).reverse.foldl
            (retStep (fun i s c => (C i s c).retAtW? i.val (W i s c)) G H) (none, s0, c0)).2.2))) := by
  subst henv hw0 hx0
  have h := evalLoop_down_retw_aux I P cond body step enc put N m hN hmN Pc C G H W hcond hP hPm hF hW hC hstep
    (N - m) N s0 c0 rfl hmN (Nat.le_refl N)
  rw [take_finRange_drop_full] at h
  exact h

/-- A fold over the positions of an array that only reads the array at the position is a fold
over its elements (the form of a `for … of` summary). -/
theorem foldl_finRange_getElem {α β : Type} (xs : Array β) (F : α → β → α) (s0 : α) :
    (List.finRange xs.size).foldl (fun s i => F s xs[i]) s0 = xs.toList.foldl F s0 := by
  have h : (List.finRange xs.size).map (fun i => xs[i]) = xs.toList := by
    apply List.ext_getElem <;> simp
  rw [← h, List.foldl_map]

/-! ### `for (const ch of str)` -/

theorem evalForOfStr_summary_cells_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (cps : List JSStr)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : JSStr → σ → κ → Completion TT ρ) (G : JSStr → σ → κ → σ) (H : JSStr → σ → κ → κ)
    (hF : ∀ ch, ch ∈ cps → ∀ s c, exec (evalB I P body (.cons (.str ch) (enc s))) (put c) =
      some (.ok (C ch s c, .cons (.str ch) (enc (G ch s c))), put (H ch s c)))
    (hC : ∀ ch s c, (C ch s c).isNext = true) :
    ∀ (l : List JSStr), (∀ ch ∈ l, ch ∈ cps) → ∀ (s : σ) (c : κ),
      exec (evalForOfStr I P l body (enc s)) (put c) =
        some (.ok (.normal, enc (l.foldl (fun p ch => (G ch p.1 p.2, H ch p.1 p.2)) (s, c)).1),
          put (l.foldl (fun p ch => (G ch p.1 p.2, H ch p.1 p.2)) (s, c)).2) := by
  intro l
  induction l with
  | nil => intro _ s c; rw [evalForOfStr.eq_1]; rfl
  | cons ch rest ih =>
    intro hsub s c
    rw [evalForOfStr.eq_2]
    simp only [exec_bind, hF ch (hsub ch (List.mem_cons_self ..)) s c, List.foldl_cons]
    rcases Completion.eq_of_isNext (hC ch s c) with h | h <;> rw [h] <;> simp only [Env.tail_cons] <;>
      exact ih (fun ch' hm => hsub ch' (List.mem_cons_of_mem _ hm)) _ _

/-- **`for (const ch of str)`, cells written.** The loop over the code points `cps` is the fold
of the body's effect; the body may use that `ch ∈ cps`. -/
theorem evalForOfStr_summary_cells (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (cps : List JSStr)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : JSStr → σ → κ → Completion TT ρ) (G : JSStr → σ → κ → σ) (H : JSStr → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hF : ∀ ch, ch ∈ cps → ∀ s c, exec (evalB I P body (.cons (.str ch) (enc s))) (put c) =
      some (.ok (C ch s c, .cons (.str ch) (enc (G ch s c))), put (H ch s c)))
    (hC : ∀ ch s c, (C ch s c).isNext = true) :
    exec (evalForOfStr I P cps body env) w =
      some (.ok (.normal, enc (cps.foldl (fun p ch => (G ch p.1 p.2, H ch p.1 p.2)) (s0, c0)).1),
        put (cps.foldl (fun p ch => (G ch p.1 p.2, H ch p.1 p.2)) (s0, c0)).2) := by
  subst henv hw0
  exact evalForOfStr_summary_cells_aux I P body cps enc put C G H hF hC cps (fun _ h => h) s0 c0

/-- **`for (const ch of str)`, world unchanged.** -/
theorem evalForOfStr_summary_pure (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (cps : List JSStr)
    {σ : Type} (enc : σ → Env TT Γ) (C : JSStr → σ → Completion TT ρ) (G : JSStr → σ → σ) (s0 : σ)
    (env : Env TT Γ) (henv : env = enc s0) (w : World TT)
    (hF : ∀ ch, ch ∈ cps → ∀ s, exec (evalB I P body (.cons (.str ch) (enc s))) w =
      some (.ok (C ch s, .cons (.str ch) (enc (G ch s))), w))
    (hC : ∀ ch s, (C ch s).isNext = true) :
    exec (evalForOfStr I P cps body env) w =
      some (.ok (.normal, enc (cps.foldl (fun s ch => G ch s) s0)), w) := by
  subst henv
  have h := evalForOfStr_summary_cells_aux I P body cps enc (fun (_ : Unit) => w) (fun ch s _ => C ch s)
    (fun ch s _ => G ch s) (fun _ _ c => c) (fun ch hm s _ => hF ch hm s) (fun ch s _ => hC ch s)
    cps (fun _ h => h) s0 ()
  simpa only [foldl_pair_const] using h

/-! ### `for (const [k, v] of map)` and `for (const x of set)` over a map the body leaves alone -/

/-- The scan behind `JSMap.nextFrom`: the next live entry and the live entries after it. -/
theorem JSMap.nextFrom_go_spec {K V : Type} :
    ∀ (l : List (Option (K × V))) (j : Nat),
      match JSMap.nextFrom.go l j with
      | none => l.filterMap id = []
      | some (j', k, v) => j ≤ j' ∧ j' < j + l.length ∧
          l.filterMap id = (k, v) :: (l.drop (j' + 1 - j)).filterMap id
  | [], j => by simp [JSMap.nextFrom.go]
  | none :: rest, j => by
    have ih := JSMap.nextFrom_go_spec rest (j + 1)
    simp only [JSMap.nextFrom.go]
    split at ih
    · next h => simpa using ih
    · next j' k v h =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨by omega, by simp; omega, ?_⟩
      have : j' + 1 - j = (j' + 1 - (j + 1)) + 1 := by omega
      rw [this, List.drop_succ_cons]
      simpa using h3
  | some (k, v) :: rest, j => by
    simp [JSMap.nextFrom.go]

theorem JSMap.nextFrom_spec {K V : Type} (m : JSMap K V) (i : Nat) :
    match m.nextFrom i with
    | none => (m.entries.drop i).filterMap id = []
    | some (j, k, v) => i ≤ j ∧ j < m.entries.length ∧
        (m.entries.drop i).filterMap id = (k, v) :: (m.entries.drop (j + 1)).filterMap id := by
  have h := JSMap.nextFrom_go_spec (m.entries.drop i) i
  unfold JSMap.nextFrom
  split at h
  · next hn => exact h
  · next j k v hs =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by simp at h2; omega, ?_⟩
    rw [h3, List.drop_drop]
    congr 3
    omega

/-- The element of a `for (const [k, v] of map)` loop for an entry. -/
abbrev mapEntryVal {k v : Ty} (kv : Val TT k × Val TT v) : Val TT (.tup (.cons k (.cons v .nil))) :=
  .tup (.cons kv.1 (.cons kv.2 .nil))

theorem evalForOfMap_summary_cells_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {k v : Ty}
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT k) (Val TT v))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → Completion TT ρ)
    (G : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → σ) (H : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → κ)
    (hcell : ∀ c, (put c).heap.get? (.map k v, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNext = true) :
    ∀ (n i : Nat) (s : σ) (c : κ), m.entries.length - i = n →
      exec (evalForOfMap I P a i body (enc s)) (put c) =
        some (.ok (.normal, enc ((((m.entries.drop i).filterMap id).map mapEntryVal).foldl
            (fun p x => (G x p.1 p.2, H x p.1 p.2)) (s, c)).1),
          put ((((m.entries.drop i).filterMap id).map mapEntryVal).foldl
            (fun p x => (G x p.1 p.2, H x p.1 p.2)) (s, c)).2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i s c hn
    rw [evalForOfMap.eq_1]
    simp only [exec_bind, exec_readMap, hcell c]
    have hspec := JSMap.nextFrom_spec m i
    split at hspec
    · next hnone => simp [hnone, hspec]
    · next j key val hsome =>
      obtain ⟨h1, h2, h3⟩ := hspec
      simp only [hsome, exec_bind, hF, h3, List.map_cons, List.foldl_cons]
      rcases Completion.eq_of_isNext (hC (.tup (.cons key (.cons val .nil))) s c) with h | h <;> rw [h] <;>
        simp only [Env.tail_cons] <;> exact ih (m.entries.length - (j + 1)) (by omega) (j + 1) _ _ rfl

/-- **`for (const [k, v] of map)`, cells written**, over a map the body leaves as `m`: the fold
over its live entries `m.toList` in insertion order. -/
theorem evalForOfMap_summary_cells (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {k v : Ty}
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT k) (Val TT v))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → Completion TT ρ)
    (G : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → σ) (H : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.map k v, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNext = true) :
    exec (evalForOfMap I P a 0 body env) w =
      some (.ok (.normal, enc (m.toList.foldl (fun p kv => (G (mapEntryVal kv) p.1 p.2, H (mapEntryVal kv) p.1 p.2))
          (s0, c0)).1),
        put (m.toList.foldl (fun p kv => (G (mapEntryVal kv) p.1 p.2, H (mapEntryVal kv) p.1 p.2)) (s0, c0)).2) := by
  subst henv hw0
  have h := evalForOfMap_summary_cells_aux I P body a m enc put C G H hcell hF hC _ 0 s0 c0 rfl
  rw [List.drop_zero, List.foldl_map] at h
  exact h

/-- **`for (const [k, v] of map)`, world unchanged.** -/
theorem evalForOfMap_summary_pure (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {k v : Ty}
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT k) (Val TT v))
    {σ : Type} (enc : σ → Env TT Γ) (C : Val TT (.tup (.cons k (.cons v .nil))) → σ → Completion TT ρ)
    (G : Val TT (.tup (.cons k (.cons v .nil))) → σ → σ) (s0 : σ)
    (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw : w.heap.get? (.map k v, a) = some m)
    (hF : ∀ x s, exec (evalB I P body (.cons x (enc s))) w = some (.ok (C x s, .cons x (enc (G x s))), w))
    (hC : ∀ x s, (C x s).isNext = true) :
    exec (evalForOfMap I P a 0 body env) w =
      some (.ok (.normal, enc (m.toList.foldl (fun s kv => G (mapEntryVal kv) s) s0)), w) := by
  have h := evalForOfMap_summary_cells I P body a m enc (fun (_ : Unit) => w) (fun x s _ => C x s)
    (fun x s _ => G x s) (fun _ _ c => c) s0 () env henv w rfl (fun _ => hw) (fun x s _ => hF x s)
    (fun x s _ => hC x s)
  simpa only [foldl_pair_const] using h

theorem evalForOfSet_summary_cells_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT t) Unit)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (hcell : ∀ c, (put c).heap.get? (.set t, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNext = true) :
    ∀ (n i : Nat) (s : σ) (c : κ), m.entries.length - i = n →
      exec (evalForOfSet I P a i body (enc s)) (put c) =
        some (.ok (.normal, enc ((((m.entries.drop i).filterMap id).map Prod.fst).foldl
            (fun p x => (G x p.1 p.2, H x p.1 p.2)) (s, c)).1),
          put ((((m.entries.drop i).filterMap id).map Prod.fst).foldl
            (fun p x => (G x p.1 p.2, H x p.1 p.2)) (s, c)).2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i s c hn
    rw [evalForOfSet.eq_1]
    simp only [exec_bind, exec_readSet, hcell c]
    have hspec := JSMap.nextFrom_spec m i
    split at hspec
    · next hnone => simp [hnone, hspec]
    · next j key u hsome =>
      obtain ⟨h1, h2, h3⟩ := hspec
      simp only [hsome, exec_bind, hF, h3, List.map_cons, List.foldl_cons]
      rcases Completion.eq_of_isNext (hC key s c) with h | h <;> rw [h] <;>
        simp only [Env.tail_cons] <;> exact ih (m.entries.length - (j + 1)) (by omega) (j + 1) _ _ rfl

/-- **`for (const x of set)`, cells written**, over a set the body leaves as `m`. -/
theorem evalForOfSet_summary_cells (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT t) Unit)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.set t, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNext = true) :
    exec (evalForOfSet I P a 0 body env) w =
      some (.ok (.normal, enc (m.toList.foldl (fun p kv => (G kv.1 p.1 p.2, H kv.1 p.1 p.2)) (s0, c0)).1),
        put (m.toList.foldl (fun p kv => (G kv.1 p.1 p.2, H kv.1 p.1 p.2)) (s0, c0)).2) := by
  subst henv hw0
  have h := evalForOfSet_summary_cells_aux I P body a m enc put C G H hcell hF hC _ 0 s0 c0 rfl
  rw [List.drop_zero, List.foldl_map] at h
  exact h

/-- **`for (const x of set)`, world unchanged.** -/
theorem evalForOfSet_summary_pure (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT t) Unit)
    {σ : Type} (enc : σ → Env TT Γ) (C : Val TT t → σ → Completion TT ρ) (G : Val TT t → σ → σ) (s0 : σ)
    (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw : w.heap.get? (.set t, a) = some m)
    (hF : ∀ x s, exec (evalB I P body (.cons x (enc s))) w = some (.ok (C x s, .cons x (enc (G x s))), w))
    (hC : ∀ x s, (C x s).isNext = true) :
    exec (evalForOfSet I P a 0 body env) w =
      some (.ok (.normal, enc (m.toList.foldl (fun s kv => G kv.1 s) s0)), w) := by
  have h := evalForOfSet_summary_cells I P body a m enc (fun (_ : Unit) => w) (fun x s _ => C x s)
    (fun x s _ => G x s) (fun _ _ c => c) s0 () env henv w rfl (fun _ => hw) (fun x s _ => hF x s)
    (fun x s _ => hC x s)
  simpa only [foldl_pair_const] using h

/-! ### `break` and `return` in loops over strings, maps and sets

The same flagged folds as for `for … of` over an array (`brkStep`, `retStep`). The tactic uses
the versions with a written cell, with `κ = Unit` when the body leaves the world unchanged. -/

theorem evalForOfStr_summary_brk_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (cps : List JSStr)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : JSStr → σ → κ → Completion TT ρ) (G : JSStr → σ → κ → σ) (H : JSStr → σ → κ → κ)
    (hF : ∀ ch, ch ∈ cps → ∀ s c, exec (evalB I P body (.cons (.str ch) (enc s))) (put c) =
      some (.ok (C ch s c, .cons (.str ch) (enc (G ch s c))), put (H ch s c)))
    (hC : ∀ ch s c, (C ch s c).isNextOrBrk = true) :
    ∀ (l : List JSStr), (∀ ch ∈ l, ch ∈ cps) → ∀ (s : σ) (c : κ),
      exec (evalForOfStr I P l body (enc s)) (put c) =
        some (.ok (.normal, enc (l.foldl (brkStep (fun ch s c => (C ch s c).isBrk0) G H) (false, s, c)).2.1),
          put (l.foldl (brkStep (fun ch s c => (C ch s c).isBrk0) G H) (false, s, c)).2.2) := by
  intro l
  induction l with
  | nil => intro _ s c; rw [evalForOfStr.eq_1]; rfl
  | cons ch rest ih =>
    intro hsub s c
    rw [evalForOfStr.eq_2]
    simp only [exec_bind, hF ch (hsub ch (List.mem_cons_self ..)) s c, List.foldl_cons]
    have ih' := ih (fun ch' hm => hsub ch' (List.mem_cons_of_mem _ hm)) (G ch s c) (H ch s c)
    rcases Completion.cases_of_isNextOrBrk (hC ch s c) with h | h | h <;> rw [h]
    · simpa [brkStep, h] using ih'
    · simpa [brkStep, h] using ih'
    · simp [brkStep, h, foldl_brkStep_done]

theorem evalForOfStr_summary_ret_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (cps : List JSStr)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : JSStr → σ → κ → Completion TT ρ) (G : JSStr → σ → κ → σ) (H : JSStr → σ → κ → κ)
    (hF : ∀ ch, ch ∈ cps → ∀ s c, exec (evalB I P body (.cons (.str ch) (enc s))) (put c) =
      some (.ok (C ch s c, .cons (.str ch) (enc (G ch s c))), put (H ch s c)))
    (hC : ∀ ch s c, (C ch s c).isNextOrRet = true) :
    ∀ (l : List JSStr), (∀ ch ∈ l, ch ∈ cps) → ∀ (s : σ) (c : κ),
      exec (evalForOfStr I P l body (enc s)) (put c) =
        some (.ok (Completion.ofRet (l.foldl (retStep (fun ch s c => (C ch s c).retVal?) G H) (none, s, c)).1,
            enc (l.foldl (retStep (fun ch s c => (C ch s c).retVal?) G H) (none, s, c)).2.1),
          put (l.foldl (retStep (fun ch s c => (C ch s c).retVal?) G H) (none, s, c)).2.2) := by
  intro l
  induction l with
  | nil => intro _ s c; rw [evalForOfStr.eq_1]; rfl
  | cons ch rest ih =>
    intro hsub s c
    rw [evalForOfStr.eq_2]
    simp only [exec_bind, hF ch (hsub ch (List.mem_cons_self ..)) s c, List.foldl_cons]
    have ih' := ih (fun ch' hm => hsub ch' (List.mem_cons_of_mem _ hm)) (G ch s c) (H ch s c)
    rcases Completion.cases_of_isNextOrRet (hC ch s c) with h | h | ⟨v, h⟩ <;> rw [h]
    · simpa [retStep, h] using ih'
    · simpa [retStep, h] using ih'
    · simp [retStep, h, foldl_retStep_done]

/-- **`for (const ch of str)` with `break`**, cells written. -/
theorem evalForOfStr_summary_cells_brk (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (cps : List JSStr)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : JSStr → σ → κ → Completion TT ρ) (G : JSStr → σ → κ → σ) (H : JSStr → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hF : ∀ ch, ch ∈ cps → ∀ s c, exec (evalB I P body (.cons (.str ch) (enc s))) (put c) =
      some (.ok (C ch s c, .cons (.str ch) (enc (G ch s c))), put (H ch s c)))
    (hC : ∀ ch s c, (C ch s c).isNextOrBrk = true) :
    exec (evalForOfStr I P cps body env) w =
      some (.ok (.normal, enc (cps.foldl (brkStep (fun ch s c => (C ch s c).isBrk0) G H) (false, s0, c0)).2.1),
        put (cps.foldl (brkStep (fun ch s c => (C ch s c).isBrk0) G H) (false, s0, c0)).2.2) := by
  subst henv hw0
  exact evalForOfStr_summary_brk_aux I P body cps enc put C G H hF hC cps (fun _ h => h) s0 c0

/-- **`for (const ch of str)` with `return`**, cells written. -/
theorem evalForOfStr_summary_cells_ret (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (cps : List JSStr)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : JSStr → σ → κ → Completion TT ρ) (G : JSStr → σ → κ → σ) (H : JSStr → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hF : ∀ ch, ch ∈ cps → ∀ s c, exec (evalB I P body (.cons (.str ch) (enc s))) (put c) =
      some (.ok (C ch s c, .cons (.str ch) (enc (G ch s c))), put (H ch s c)))
    (hC : ∀ ch s c, (C ch s c).isNextOrRet = true) :
    exec (evalForOfStr I P cps body env) w =
      some (.ok (Completion.ofRet (cps.foldl (retStep (fun ch s c => (C ch s c).retVal?) G H) (none, s0, c0)).1,
          enc (cps.foldl (retStep (fun ch s c => (C ch s c).retVal?) G H) (none, s0, c0)).2.1),
        put (cps.foldl (retStep (fun ch s c => (C ch s c).retVal?) G H) (none, s0, c0)).2.2) := by
  subst henv hw0
  exact evalForOfStr_summary_ret_aux I P body cps enc put C G H hF hC cps (fun _ h => h) s0 c0

theorem evalForOfMap_summary_brk_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {k v : Ty}
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT k) (Val TT v))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → Completion TT ρ)
    (G : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → σ) (H : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → κ)
    (hcell : ∀ c, (put c).heap.get? (.map k v, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrBrk = true) :
    ∀ (n i : Nat) (s : σ) (c : κ), m.entries.length - i = n →
      exec (evalForOfMap I P a i body (enc s)) (put c) =
        some (.ok (.normal, enc ((((m.entries.drop i).filterMap id).map mapEntryVal).foldl
            (brkStep (fun x s c => (C x s c).isBrk0) G H) (false, s, c)).2.1),
          put ((((m.entries.drop i).filterMap id).map mapEntryVal).foldl
            (brkStep (fun x s c => (C x s c).isBrk0) G H) (false, s, c)).2.2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i s c hn
    rw [evalForOfMap.eq_1]
    simp only [exec_bind, exec_readMap, hcell c]
    have hspec := JSMap.nextFrom_spec m i
    split at hspec
    · next hnone => simp [hnone, hspec]
    · next j key val hsome =>
      obtain ⟨h1, h2, h3⟩ := hspec
      simp only [hsome, exec_bind, hF, h3, List.map_cons, List.foldl_cons]
      have ih' := ih (m.entries.length - (j + 1)) (by omega) (j + 1)
        (G (.tup (.cons key (.cons val .nil))) s c) (H (.tup (.cons key (.cons val .nil))) s c) rfl
      rcases Completion.cases_of_isNextOrBrk (hC (.tup (.cons key (.cons val .nil))) s c) with h | h | h <;> rw [h]
      · simpa [brkStep, h] using ih'
      · simpa [brkStep, h] using ih'
      · simp [brkStep, h, foldl_brkStep_done]

theorem evalForOfMap_summary_ret_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {k v : Ty}
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT k) (Val TT v))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → Completion TT ρ)
    (G : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → σ) (H : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → κ)
    (hcell : ∀ c, (put c).heap.get? (.map k v, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrRet = true) :
    ∀ (n i : Nat) (s : σ) (c : κ), m.entries.length - i = n →
      exec (evalForOfMap I P a i body (enc s)) (put c) =
        some (.ok (Completion.ofRet ((((m.entries.drop i).filterMap id).map mapEntryVal).foldl
              (retStep (fun x s c => (C x s c).retVal?) G H) (none, s, c)).1,
            enc ((((m.entries.drop i).filterMap id).map mapEntryVal).foldl
              (retStep (fun x s c => (C x s c).retVal?) G H) (none, s, c)).2.1),
          put ((((m.entries.drop i).filterMap id).map mapEntryVal).foldl
            (retStep (fun x s c => (C x s c).retVal?) G H) (none, s, c)).2.2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i s c hn
    rw [evalForOfMap.eq_1]
    simp only [exec_bind, exec_readMap, hcell c]
    have hspec := JSMap.nextFrom_spec m i
    split at hspec
    · next hnone => simp [hnone, hspec]
    · next j key val hsome =>
      obtain ⟨h1, h2, h3⟩ := hspec
      simp only [hsome, exec_bind, hF, h3, List.map_cons, List.foldl_cons]
      have ih' := ih (m.entries.length - (j + 1)) (by omega) (j + 1)
        (G (.tup (.cons key (.cons val .nil))) s c) (H (.tup (.cons key (.cons val .nil))) s c) rfl
      rcases Completion.cases_of_isNextOrRet (hC (.tup (.cons key (.cons val .nil))) s c) with h | h | ⟨r, h⟩ <;>
        rw [h]
      · simpa [retStep, h] using ih'
      · simpa [retStep, h] using ih'
      · simp [retStep, h, foldl_retStep_done]

/-- **`for (const [k, v] of map)` with `break`**, cells written. -/
theorem evalForOfMap_summary_cells_brk (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {k v : Ty}
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT k) (Val TT v))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → Completion TT ρ)
    (G : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → σ) (H : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.map k v, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrBrk = true) :
    exec (evalForOfMap I P a 0 body env) w =
      some (.ok (.normal, enc ((m.toList.map mapEntryVal).foldl (brkStep (fun x s c => (C x s c).isBrk0) G H)
          (false, s0, c0)).2.1),
        put ((m.toList.map mapEntryVal).foldl (brkStep (fun x s c => (C x s c).isBrk0) G H) (false, s0, c0)).2.2) := by
  subst henv hw0
  have h := evalForOfMap_summary_brk_aux I P body a m enc put C G H hcell hF hC _ 0 s0 c0 rfl
  rw [List.drop_zero] at h
  exact h

/-- **`for (const [k, v] of map)` with `return`**, cells written. -/
theorem evalForOfMap_summary_cells_ret (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {k v : Ty}
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT k) (Val TT v))
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → Completion TT ρ)
    (G : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → σ) (H : Val TT (.tup (.cons k (.cons v .nil))) → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.map k v, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrRet = true) :
    exec (evalForOfMap I P a 0 body env) w =
      some (.ok (Completion.ofRet ((m.toList.map mapEntryVal).foldl (retStep (fun x s c => (C x s c).retVal?) G H)
            (none, s0, c0)).1,
          enc ((m.toList.map mapEntryVal).foldl (retStep (fun x s c => (C x s c).retVal?) G H) (none, s0, c0)).2.1),
        put ((m.toList.map mapEntryVal).foldl (retStep (fun x s c => (C x s c).retVal?) G H) (none, s0, c0)).2.2) := by
  subst henv hw0
  have h := evalForOfMap_summary_ret_aux I P body a m enc put C G H hcell hF hC _ 0 s0 c0 rfl
  rw [List.drop_zero] at h
  exact h

theorem evalForOfSet_summary_brk_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT t) Unit)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (hcell : ∀ c, (put c).heap.get? (.set t, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrBrk = true) :
    ∀ (n i : Nat) (s : σ) (c : κ), m.entries.length - i = n →
      exec (evalForOfSet I P a i body (enc s)) (put c) =
        some (.ok (.normal, enc ((((m.entries.drop i).filterMap id).map Prod.fst).foldl
            (brkStep (fun x s c => (C x s c).isBrk0) G H) (false, s, c)).2.1),
          put ((((m.entries.drop i).filterMap id).map Prod.fst).foldl
            (brkStep (fun x s c => (C x s c).isBrk0) G H) (false, s, c)).2.2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i s c hn
    rw [evalForOfSet.eq_1]
    simp only [exec_bind, exec_readSet, hcell c]
    have hspec := JSMap.nextFrom_spec m i
    split at hspec
    · next hnone => simp [hnone, hspec]
    · next j key u hsome =>
      obtain ⟨h1, h2, h3⟩ := hspec
      simp only [hsome, exec_bind, hF, h3, List.map_cons, List.foldl_cons]
      have ih' := ih (m.entries.length - (j + 1)) (by omega) (j + 1) (G key s c) (H key s c) rfl
      rcases Completion.cases_of_isNextOrBrk (hC key s c) with h | h | h <;> rw [h]
      · simpa [brkStep, h] using ih'
      · simpa [brkStep, h] using ih'
      · simp [brkStep, h, foldl_brkStep_done]

theorem evalForOfSet_summary_ret_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT t) Unit)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (hcell : ∀ c, (put c).heap.get? (.set t, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrRet = true) :
    ∀ (n i : Nat) (s : σ) (c : κ), m.entries.length - i = n →
      exec (evalForOfSet I P a i body (enc s)) (put c) =
        some (.ok (Completion.ofRet ((((m.entries.drop i).filterMap id).map Prod.fst).foldl
              (retStep (fun x s c => (C x s c).retVal?) G H) (none, s, c)).1,
            enc ((((m.entries.drop i).filterMap id).map Prod.fst).foldl
              (retStep (fun x s c => (C x s c).retVal?) G H) (none, s, c)).2.1),
          put ((((m.entries.drop i).filterMap id).map Prod.fst).foldl
            (retStep (fun x s c => (C x s c).retVal?) G H) (none, s, c)).2.2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i s c hn
    rw [evalForOfSet.eq_1]
    simp only [exec_bind, exec_readSet, hcell c]
    have hspec := JSMap.nextFrom_spec m i
    split at hspec
    · next hnone => simp [hnone, hspec]
    · next j key u hsome =>
      obtain ⟨h1, h2, h3⟩ := hspec
      simp only [hsome, exec_bind, hF, h3, List.map_cons, List.foldl_cons]
      have ih' := ih (m.entries.length - (j + 1)) (by omega) (j + 1) (G key s c) (H key s c) rfl
      rcases Completion.cases_of_isNextOrRet (hC key s c) with h | h | ⟨r, h⟩ <;> rw [h]
      · simpa [retStep, h] using ih'
      · simpa [retStep, h] using ih'
      · simp [retStep, h, foldl_retStep_done]

/-- **`for (const x of set)` with `break`**, cells written. -/
theorem evalForOfSet_summary_cells_brk (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT t) Unit)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.set t, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrBrk = true) :
    exec (evalForOfSet I P a 0 body env) w =
      some (.ok (.normal, enc ((m.toList.map Prod.fst).foldl (brkStep (fun x s c => (C x s c).isBrk0) G H)
          (false, s0, c0)).2.1),
        put ((m.toList.map Prod.fst).foldl (brkStep (fun x s c => (C x s c).isBrk0) G H) (false, s0, c0)).2.2) := by
  subst henv hw0
  have h := evalForOfSet_summary_brk_aux I P body a m enc put C G H hcell hF hC _ 0 s0 c0 rfl
  rw [List.drop_zero] at h
  exact h

/-- **`for (const x of set)` with `return`**, cells written. -/
theorem evalForOfSet_summary_cells_ret (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (m : JSMap (Val TT t) Unit)
    {σ κ : Type} (enc : σ → Env TT Γ) (put : κ → World TT)
    (C : Val TT t → σ → κ → Completion TT ρ) (G : Val TT t → σ → κ → σ) (H : Val TT t → σ → κ → κ)
    (s0 : σ) (c0 : κ) (env : Env TT Γ) (henv : env = enc s0) (w : World TT) (hw0 : w = put c0)
    (hcell : ∀ c, (put c).heap.get? (.set t, a) = some m)
    (hF : ∀ x s c, exec (evalB I P body (.cons x (enc s))) (put c) =
      some (.ok (C x s c, .cons x (enc (G x s c))), put (H x s c)))
    (hC : ∀ x s c, (C x s c).isNextOrRet = true) :
    exec (evalForOfSet I P a 0 body env) w =
      some (.ok (Completion.ofRet ((m.toList.map Prod.fst).foldl (retStep (fun x s c => (C x s c).retVal?) G H)
            (none, s0, c0)).1,
          enc ((m.toList.map Prod.fst).foldl (retStep (fun x s c => (C x s c).retVal?) G H) (none, s0, c0)).2.1),
        put ((m.toList.map Prod.fst).foldl (retStep (fun x s c => (C x s c).retVal?) G H) (none, s0, c0)).2.2) := by
  subst henv hw0
  have h := evalForOfSet_summary_ret_aux I P body a m enc put C G H hcell hF hC _ 0 s0 c0 rfl
  rw [List.drop_zero] at h
  exact h

end StrictTS

/-! ### The `ts_summarize` tactic -/

namespace StrictTS.Summarize
open Lean Meta Elab Tactic

/-- The slots of a context (a list literal up to `whnf`), each with the tail after it. -/
partial def ctxSpine (Γ : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let Γ' ← whnf Γ
  match Γ'.getAppFnArgs with
  | (``List.cons, #[_, s, rest]) => do
    let rest' ← whnf rest
    return #[(s, rest')] ++ (← ctxSpine rest')
  | (``List.nil, _) => return #[]
  | _ => throwError "ts_summarize: the loop's context is not a list literal: {Γ}"

/-- The components of an environment: constructor arguments if it is a literal, else
`head`/`tail` projections. -/
partial def envComps (env : Lean.Expr) (n : Nat) : MetaM (Array Lean.Expr) := do
  if n == 0 then return #[]
  let e ← whnfR (← instantiateMVars env)
  match e.getAppFnArgs with
  | (``Env.cons, #[_, _, _, v, rest]) => return #[v] ++ (← envComps rest (n - 1))
  | _ => do
    let hd ← mkAppM ``Env.head #[env]
    let tl ← mkAppM ``Env.tail #[env]
    return #[hd] ++ (← envComps tl (n - 1))

/-- Right-nested product of types (`Unit` if empty). -/
def mkProdTy : List Lean.Expr → MetaM Lean.Expr
  | [] => return mkConst ``Unit
  | [t] => return t
  | t :: ts => do mkAppM ``Prod #[t, ← mkProdTy ts]

/-- Right-nested tuple. -/
def mkTuple : List Lean.Expr → MetaM Lean.Expr
  | [] => return mkConst ``Unit.unit
  | [v] => return v
  | v :: vs => do mkAppM ``Prod.mk #[v, ← mkTuple vs]

/-- The components of a right-nested tuple `s` with `m` components. -/
def tupleProjs (s : Lean.Expr) : Nat → MetaM (List Lean.Expr)
  | 0 => return []
  | 1 => return [s]
  | m + 1 => do
    let p1 ← mkAppM ``Prod.fst #[s]
    let p2 ← mkAppM ``Prod.snd #[s]
    return p1 :: (← tupleProjs p2 m)

/-- The slots of the loop's environment (`0` = innermost) that the blocks `bs` assign, the
blocks being under `d` declarations of their own (the element of a `for … of`); `none` when a
construct is not understood (then every mutable slot counts as assigned). A mutable variable
that the loop never assigns keeps its value: the summaries leave it out of the fold's state, so
the body sees its value (an enclosing loop's counter, for a nested loop). -/
partial def assignedSlots (bs : Array (Lean.Expr × Nat)) : MetaM (Option (Array Nat)) := do
  let out ← IO.mkRef (#[] : Array Nat)
  let rec pos (e : Lean.Expr) : MetaM (Option Nat) := do
    let e ← whnfR e
    if e.isAppOf ``MVar.here then return some 0
    if e.isAppOf ``MVar.there then return (← pos e.appArg!).map (· + 1)
    return none
  let rec go (e : Lean.Expr) (d : Nat) : MetaM Bool := do
    let e ← whnfR e
    let n := e.getAppNumArgs
    let arg (i : Nat) := e.getArg! i
    match e.getAppFn.constName? with
    | some ``Block.nil => return true
    | some ``Block.seq => return (← go (arg 3) d) && (← go (arg 4) d)
    | some ``Block.decl => go (arg 5) (d + 1)
    | some ``Block.await => go (arg 5) (d + 1)
    | some ``Stmt.assign =>
      match ← pos (arg 4) with
      | some k =>
        if k ≥ d then out.modify (·.push (k - d))
        return true
      | none => return false
    | some ``Stmt.expr | some ``Stmt.gset | some ``Stmt.setField | some ``Stmt.brk | some ``Stmt.cont
    | some ``Stmt.ret | some ``Stmt.retP | some ``Stmt.throw => return true
    | some ``Stmt.ite => return (← go (arg 4) d) && (← go (arg 5) d)
    | some ``Stmt.while => go (arg 4) d
    | some ``Stmt.doWhile => go (arg 3) d
    | some ``Stmt.forLoop => return (← go (arg 4) d) && (← go (arg 5) d)
    | some ``Stmt.forOf => go (arg 5) (d + 1)
    | some ``Stmt.forOfMap => go (arg 6) (d + 1)
    | some ``Stmt.forOfSet => go (arg 5) (d + 1)
    | some ``Stmt.forOfStr => go (arg 4) (d + 1)
    | some ``Stmt.try => return (← go (arg 3) d) && (← go (arg 4) (d + 1)) && (← go (arg 5) d)
    | some ``Stmt.tryFin => return (← go (arg 3) d) && (← go (arg 4) d)
    | some ``Stmt.caseOptS => return (← go (arg 5) d) && (← go (arg 6) (d + 1))
    | some ``Stmt.caseUS => go (arg 5) d
    | some ``AltsS.nil => return true
    | some ``AltsS.cons => return (← go (arg 5) (d + 1)) && (← go (arg 6) d)
    | some ``Stmt.block | some ``Stmt.breakable => if n ≥ 4 then go (arg 3) d else return false
    | _ => return false
  for (b, d) in bs do
    unless ← go b d do return none
  return some (← out.get)

/-- The values of the mutable slots `mutIdx` (in order) for an environment literal: the
counter `cnt` at slot `j`, the state's projections `ps` at the slots `stateIdx`, the start
value `comps[i]` at a slot the loop does not assign. -/
def mutVals (mutIdx stateIdx : List Nat) (comps ps : Array Lean.Expr) (cnt? : Option (Nat × Lean.Expr)) :
    List Lean.Expr := Id.run do
  let mut out := #[]
  let mut q := 0
  for i in mutIdx do
    if let some (j, cnt) := cnt? then
      if i == j then
        out := out.push cnt
        continue
    if stateIdx.contains i then
      out := out.push ps[q]!
      q := q + 1
    else out := out.push comps[i]!
  return out.toList

/-- The environment literal whose mutable slots are `muts` (in order) and whose `const` slots
are the given values. -/
def mkEnvLit (TT : Lean.Expr) (spine : Array (Lean.Expr × Lean.Expr)) (isMut : Array Bool) (consts : Array Lean.Expr)
    (muts : List Lean.Expr) : MetaM Lean.Expr := do
  let mut out := mkApp (mkConst ``Env.nil) TT
  let mut ms := muts.toArray
  -- build from the right
  let mut j := ms.size
  for i' in [0:spine.size] do
    let i := spine.size - 1 - i'
    let (s, tail) := spine[i]!
    let c ← if isMut[i]! then do j := j - 1; pure ms[j]! else pure consts[i]!
    out := mkAppN (mkConst ``Env.cons) #[TT, s, tail, c, out]
  return out

/-- What a `match` in a symbolic result is stuck on. -/
inductive Stuck where
  /-- the condition of an `if` -/
  | cond (c : Lean.Expr)
  /-- an optional value that is not a constructor (with its element type) -/
  | opt (d α : Lean.Expr)

/-- A `match` in `e` (outside binders) stuck on an `if` or on a symbolic optional value; the
innermost such discriminant is chosen (outer ones are stuck only because of it). -/
def findStuck (e : Lean.Expr) : MetaM (Option Stuck) := do
  let found ← IO.mkRef (#[] : Array (Lean.Expr × Stuck))
  -- `forEachExpr` enters binders with fresh local variables: a discriminant that mentions one
  -- is under a binder
  let lctx ← getLCtx
  Meta.forEachExpr e fun sub => do
    if sub.hasLooseBVars then return
    let some app ← matchMatcherApp? sub | return
    for d in app.discrs do
      -- (elaborated terms carry `save_info` annotations)
      let d := (← instantiateMVars d).consumeMData
      if d.hasLooseBVars || d.hasAnyFVar (!lctx.contains ·) then continue
      if d.isAppOfArity ``ite 5 || d.isAppOfArity ``dite 5 then
        found.modify (·.push (d, .cond (d.getArg! 1)))
      else if !(d.isAppOf ``Option.none || d.isAppOf ``Option.some) then
        let ty ← whnfR (← inferType d)
        if ty.isAppOfArity ``Option 1 then found.modify (·.push (d, .opt d ty.appArg!))
  let cands ← found.get
  let inner := cands.filter fun (d, _) =>
    !cands.any fun (d', _) => d' != d && (d.find? (· == d')).isSome
  let pick : Option (Lean.Expr × Stuck) := if inner.isEmpty then cands[0]? else inner[0]?
  return pick.map (fun p => p.2)

/-- An `if` (outside binders) whose two branches are applications of the same function: the
`if` can be pushed inside. -/
def findPushableIte (e : Lean.Expr) : Option Lean.Expr :=
  e.find? fun sub =>
    sub.isAppOfArity ``ite 5 && !sub.hasLooseBVars &&
      (let a := (sub.getArg! 3).consumeMData
       let b := (sub.getArg! 4).consumeMData
       a != b && a.isApp && a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs &&
         !a.getAppFn.isMVar)

/-- Anti-unification of the results of two paths: equal parts are shared, applications of the
same function are merged argument by argument (when the result type-checks), and the
remaining differences are combined by `mk`. -/
partial def antiUnify (mk : Lean.Expr → Lean.Expr → MetaM Lean.Expr) (a b : Lean.Expr) : MetaM Lean.Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return a
  let fa := a.getAppFn
  if fa == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 && !fa.isMVar then
    let mut args := #[]
    for (x, y) in a.getAppArgs.zip b.getAppArgs do
      args := args.push (← antiUnify mk x y)
    let r := mkAppN fa args
    if (← try Meta.check r; pure true catch _ => pure false) then return r
  mk a b

end StrictTS.Summarize

namespace StrictTS
open Lean Elab Tactic Meta Summarize

/-- `ts_summarize [lemmas] xs` rewrites the first `for (const x of arr)` loop in the goal, over an
array holding `xs` (if `xs` is omitted, it is read off the hypotheses), into a left fold of the
body's effect. The optional `lemmas` are added to the symbolic execution of the body (e.g. the
contract of a function the body calls: `∀ x w, exec (callFun I P fRef (.cons x .nil)) w = …`). The state of the fold is the tuple of the values of the mutable variables in scope
(const variables never change) and, if the body writes a heap cell (`push`, `Map.set`, a field),
that cell's content. The step function is computed by symbolic execution of the body on a
symbolic state, with conditions merged into `if`s, so no invariant is needed. Applies when every
iteration completes normally or with `continue`. Side goals that `simp` cannot close (the
array cell, the written cell's existence) are left to the user.

If the first loop in the goal is a counted loop `for (let i = k0; i < n; i++)` (`n` an array
length or a constant, fixed during the loop; the counter is assigned only by the step), it is
rewritten into the fold of the body's effect over the positions `k0 … n-1`
(`(List.finRange n).drop k0`), with the counter ending at `ofNat n`; when the body uses the
counter only to read `xs[i]` and the loop covers all of `xs`, into the fold over the elements,
as for `for … of`. The body sees the counter as a valid index of `xs` when a hypothesis bounds
`xs.size` below `2^32` (JavaScript arrays are shorter). -/
syntax (name := tsSummarize) "ts_summarize" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (ppSpace colGt term)? :
  tactic

/-- `ts_callbacks [lemmas] xs` rewrites the first call of an array method with a callback in the
goal, over an array holding `xs` (if omitted, read off the hypotheses), into the standard
function of the callback's meaning `g`, computed by symbolic execution of the callback (with the
heap hypotheses and the optional `lemmas`, e.g. the contract of a function the callback calls):
`reduce ↦ List.foldl g init`, `map ↦ Array.map g`, `filter ↦ Array.filter`, `some ↦ Array.any`,
`every ↦ Array.all`, `find ↦ Array.find?`, `findIndex ↦ Array.findIdx?`, `findLast`/`findLastIndex`
(the same on the reversed array), `forEach` (no effect) and `sort ↦ sortBy` (the array is
sorted in place). Applies when the callback uses only its first arguments (accumulator and
element for `reduce`, both elements for a comparator, the element otherwise) and leaves the
world unchanged in every world. Side goals it cannot close by `simp` (the array cell; for `map`
and `filter`, that the array is not at the next fresh address) are left to the user. -/
syntax (name := tsCallbacks) "ts_callbacks" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (ppSpace colGt term)? :
  tactic

/-- `ts_summarize`/`ts_callbacks` called from inside another one's symbolic execution (a nested
loop, a callback in a loop body): such a call leaves the enclosing call's heap facts in place. -/
def Summarize.nested : CoreM Bool := return (← getOptions).getBool `strictts_nested false

/-- Run `k` as a nested summarization (`Summarize.nested`). -/
def Summarize.withNested {α : Type} (k : TacticM α) : TacticM α :=
  withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `strictts_nested true }) k

/-- The first loop or array method with a callback that the left side `lhs` of a symbolic
execution goal runs (`some true` for a loop, `some false` for a callback). -/
def Summarize.nestedRun? (lhs : Lean.Expr) : Option Bool :=
  let loops := #[``evalForOf, ``evalLoop, ``evalForOfStr, ``evalForOfMap, ``evalForOfSet]
  let cbs := #[``Builtin.arrFilter, ``Builtin.arrSome, ``Builtin.arrEvery, ``Builtin.arrFind,
    ``Builtin.arrFindIndex, ``Builtin.arrFindLast, ``Builtin.arrFindLastIndex, ``Builtin.arrReduce,
    ``Builtin.arrMap, ``Builtin.arrForEach, ``Builtin.arrSort]
  let hit := lhs.find? fun e => e.isAppOfArity ``JS.exec 4 && !e.hasLooseBVars &&
    (loops.any (e.getArg! 2).isAppOf ||
      ((e.getArg! 2).isAppOf ``evalBuiltin && (e.getArg! 2).getAppNumArgs ≥ 6 &&
        cbs.any (((e.getArg! 2).getArg! 5).isAppOf ·)))
  hit.map fun e => loops.any (e.getArg! 2).isAppOf

/-- One merge round on the main goal `lhs = rhs` (see `ts_merge`); `hyps` are the branch
conditions in scope. -/
partial def mergeGoal (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (hyps : Array Ident)
    (depth : Nat) : TacticM Unit := do
  let lemmas := extra ++ (← hyps.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident))
  let mainPass : TacticM Unit := do
    try evalTactic (← `(tactic|
      simp only [ts_sym, ne_eq, reduceCtorEq, not_false_eq_true, Env.get_here', Env.get_there', Env.set_here', Env.set_there', Env.getC_here',
        Env.getC_there', Env.head_cons, Env.tail_cons, Merge.ite_some, Merge.ite_pair, Merge.ite_ok,
        Merge.ite_cons, ite_self, Merge.optCase_none, Merge.optCase_some, $lemmas,*]))
    catch _ => pure ()
  let simpStep : TacticM Unit := do
    mainPass
    -- the default discharger leaves numeric side conditions of the caller's lemmas open
    -- (`n ≤ 2 ^ 53` in a lemma about `F64.ofNat n`): a second pass with only those lemmas,
    -- then the main pass again if it rewrote something
    unless extra.isEmpty do
      let some g := (← getGoals).head? | return
      try evalTactic (← `(tactic| simp (disch := first | decide | omega) only [$extra,*]))
      catch _ => pure ()
      if let some g' := (← getGoals).head? then
        if g' != g then mainPass
  simpStep
  if (← getGoals).isEmpty then return
  try
    evalTactic (← `(tactic| rfl))
    return
  catch _ => pure ()
  if depth ≥ 6 then return
  -- a loop or an array method with a callback in the code being evaluated (a loop in a loop
  -- body, `every` in a callback): summarize it on the symbolic state with this merge's lemmas,
  -- then go on; the summary must leave no side goal
  let nested? ← withMainContext do
    let goal := (← instantiateMVars (← getMainTarget)).consumeMData
    let some (_, lhs, _) := goal.eq? | return none
    return Summarize.nestedRun? lhs
  if let some isLoop := nested? then
    let saved ← saveState
    let n := (← getGoals).length
    -- (the summaries find their obligations by tag: the enclosing goal's tag, e.g. `hF`, must
    -- not be taken for one of them)
    let g0 ← getMainGoal
    let tag0 ← g0.getTag
    g0.setTag `nested_body
    let ok ← try
        Summarize.withNested do
          if isLoop then evalTactic (← `(tactic| ts_summarize [$lemmas,*]))
          else evalTactic (← `(tactic| ts_callbacks [$lemmas,*]))
        if let some g := (← getGoals).head? then g.setTag tag0
        pure ((← getGoals).length == n)
      catch _ => pure false
    if ok then
      mergeGoal extra hyps (depth + 1)
      return
    saved.restore
  let some (st, α) ← withMainContext do
      let goal := (← instantiateMVars (← getMainTarget)).consumeMData
      let some (α, lhs, _) := goal.eq? | return none
      return (← findStuck lhs).map (·, α)
    | -- no stuck `match`: push a remaining `if` inside (e.g. between two worlds), then retry
      let pushed ← withMainContext do
        let goal := (← instantiateMVars (← getMainTarget)).consumeMData
        let some (_, lhs, _) := goal.eq? | return none
        let some it := findPushableIte lhs | return none
        let c := it.getArg! 1
        let merged ← antiUnify (fun x y => mkAppOptM ``ite #[none, c, none, x, y])
          (it.getArg! 3) (it.getArg! 4)
        if merged == it then return none
        return some (← Term.exprToSyntax it, ← Term.exprToSyntax merged, ← Term.exprToSyntax c)
      let some (itS, mS, cS) := pushed | return
      evalTactic (← `(tactic| rw [show $itS = $mS by
        by_cases hcm : $cS <;>
        first
        | (simp only [ite_eq_left_of_eq_true _ _ (eq_true hcm)]; done)
        | (simp only [ite_eq_right_of_eq_false _ _ (eq_false hcm)]; done)
        | (simp only [hcm, ↓reduceIte, ite_true, ite_false, not_false_eq_true]; done)]))
      mergeGoal extra hyps (depth + 1)
      return
  -- a condition that `omega` decides from the hypotheses (an array bound with a `Fin` counter,
  -- `↑i < xs.size`): take that branch instead of splitting. The branch conditions of enclosing
  -- splits are cleared for `omega`, so the proof term mentions only variables in scope of the
  -- values being read off; if the branch still does not reduce to a value, split as before.
  if let .cond c := st then
    let cS ← withMainContext <| Term.exprToSyntax c
    let saved0 ← saveState
    let gs0 ← getGoals
    -- (sizes of updated arrays: `(xs.set j v).size` is `xs.size`)
    let (pos, neg) ← if hyps.isEmpty then
        pure (← `(show $cS by first | omega | (simp only [Array.size_set, Array.size_setIfInBounds,
            Array.size_push, StrictTS.sized_size] at *; omega)),
          ← `(show ¬ $cS by first | omega | (simp only [Array.size_set, Array.size_setIfInBounds,
            Array.size_push, StrictTS.sized_size] at *; omega)))
      else
        pure (← `(show $cS by clear $hyps*; first | omega | (simp only [Array.size_set,
            Array.size_setIfInBounds, Array.size_push, StrictTS.sized_size] at *; omega)),
          ← `(show ¬ $cS by clear $hyps*; first | omega | (simp only [Array.size_set,
            Array.size_setIfInBounds, Array.size_push, StrictTS.sized_size] at *; omega)))
    let mut decided := false
    for tac in [← `(tactic| simp only [dite_eq_left $pos, ite_eq_left $pos]),
        ← `(tactic| simp only [dite_eq_right $neg, ite_eq_right $neg])] do
      unless decided do
        try
          evalTactic tac
          decided := true
        catch _ => saved0.restore
    if decided then
      try
        mergeGoal extra hyps depth
        if (← getGoals) == gs0.tail then return
      catch _ => pure ()
      saved0.restore
  let hc := mkIdent (Name.mkSimple s!"hc_merge_{depth}")
  let vI := mkIdent (Name.mkSimple s!"v_merge_{depth}")
  -- the values of the two paths, read off by the recursive calls
  let (A, B) ← withMainContext do
    let A ← mkFreshExprMVar α
    let B ← match st with
      | .cond _ => mkFreshExprMVar α
      | .opt _ el => do mkFreshExprMVar (← mkArrow el α)
    return (A, B)
  let (AS, BS) ← withMainContext do return (← Term.exprToSyntax A, ← Term.exprToSyntax B)
  -- a discriminant the split lemmas cannot abstract (e.g. a `match` inside a monadic term that
  -- depends on the loop state): leave the goal to the caller, which reports it as stuck
  let saved ← saveState
  try
    match st with
    | .cond c => do
      let cS ← withMainContext <| Term.exprToSyntax c
      evalTactic (← `(tactic| refine Eq.trans (Merge.split_ite (c := $cS)) ?_))
      evalTactic (← `(tactic|
        refine Eq.trans (Merge.ite_congr' (a' := $AS) (b' := $BS) (fun $hc => ?_) (fun $hc => ?_)) ?_))
    | .opt d _ => do
      let dS ← withMainContext <| Term.exprToSyntax d
      evalTactic (← `(tactic| refine Eq.trans (Merge.split_opt (d := $dS)) ?_))
      evalTactic (← `(tactic|
        refine Eq.trans (Merge.optCase_congr (a' := $AS) (b' := $BS) (fun $hc => ?_) (fun $vI $hc => ?_)) ?_))
  catch _ =>
    saved.restore
    return
  -- goals: the two paths, then the merged goal
  let gls ← getGoals
  let (paths, main) := (gls.take 2, gls.drop 2)
  for b in paths do
    setGoals [b]
    -- a path that does not reduce to a value: the goal stays as it was, for the caller to
    -- report (a summary then retries with the cell the path writes)
    let ok ← try
        mergeGoal extra (hyps.push hc) (depth + 1)
        pure (← getGoals).isEmpty
      catch _ => pure false
    unless ok do
      saved.restore
      return
  setGoals main
  -- one value for both paths: anti-unify them, prove the merge by case analysis
  let merged? ← withMainContext do
    let A ← instantiateMVars A
    let B ← instantiateMVars B
    match st with
    | .cond c =>
      some <$> antiUnify (fun x y => mkAppOptM ``ite #[none, c, none, x, y]) A B
    | .opt d el =>
      withLocalDeclD `v el fun v => do
        let Bv := (B.beta #[v]).headBeta
        let r ← antiUnify (fun x y => do
            mkAppM ``Merge.optCase #[d, x, ← mkLambdaFVars #[v] y]) A Bv
        if r.containsFVar v.fvarId! then return none
        return some r
  if let some merged := merged? then
    let mS ← withMainContext <| Term.exprToSyntax merged
    evalTactic (← `(tactic| refine Eq.trans (b := $mS) ?_ ?_))
    let gls ← getGoals
    setGoals [gls.head!]
    match st with
    | .cond c => do
      let cS ← withMainContext <| Term.exprToSyntax c
      evalTactic (← `(tactic| (by_cases hcm : $cS <;>
        first
        | (simp only [ite_eq_left_of_eq_true _ _ (eq_true hcm)]; done)
        | (simp only [ite_eq_right_of_eq_false _ _ (eq_false hcm)]; done)
        | (simp only [hcm, ↓reduceIte, ite_true, ite_false, not_false_eq_true]; done))))
    | .opt d _ => do
      let dS ← withMainContext <| Term.exprToSyntax d
      evalTactic (← `(tactic| (generalize $dS = om; cases om <;> rfl)))
    unless (← getGoals).isEmpty do
      throwError "ts_merge: could not prove the merge of two paths; remaining goal:\n{← ppGoal (← getMainGoal)}"
    setGoals gls.tail!
  mergeGoal extra hyps depth

/-- `ts_merge [simp lemmas]` closes a goal `lhs = rhs` whose right side has metavariables
(the effect to be read off): `simp` evaluates `lhs`; while a `match` is stuck on a symbolic
condition `c`, the goal is split on `c` **inside one goal** (`lhs = if c then lhs else lhs`,
each branch evaluated under its condition, then path merging), so that the result is one
value with `if`s in it; finally `rfl` assigns the metavariables. -/
elab "ts_merge " "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  mergeGoal extra.getElems #[] 0

end StrictTS

namespace StrictTS
open Lean Elab Tactic Meta Summarize

/-- Hypotheses about heap cells in the local context, as simp lemmas (they evaluate reads of
cells the loop does not write). -/
def heapHyps : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := withMainContext do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, lhs, _) := ty.eq? then
      if lhs.isAppOf ``Std.ExtDHashMap.get? then
        let t ← Term.exprToSyntax (mkFVar d.fvarId)
        out := out.push (← `(Lean.Parser.Tactic.simpLemma| $t:term))
  return out

/-- The keys of the cells written by one iteration: `insert K v` in `e` with `v` mentioning a
variable of the iteration (`locals`) and `K` mentioning none. -/
def writtenCells (e : Lean.Expr) (locals : Array FVarId) : MetaM (Array Lean.Expr) := do
  let out ← IO.mkRef (#[] : Array Lean.Expr)
  let mentions (x : Lean.Expr) := x.hasAnyFVar (locals.contains ·)
  -- (`forEachExpr` enters binders with fresh local variables: keys that mention one are skipped)
  let lctx ← getLCtx
  Meta.forEachExpr e fun sub => do
    if sub.isAppOf ``Std.ExtDHashMap.insert && sub.getAppNumArgs ≥ 2 then
      let n := sub.getAppNumArgs
      let K := sub.getArg! (n - 2)
      let v := sub.getArg! (n - 1)
      -- a key is a pair `(kind, address)` (this also skips partial applications of `insert`)
      if K.isAppOfArity ``Prod.mk 4 && mentions v && !mentions K && !K.hasLooseBVars &&
          !K.hasAnyFVar (!lctx.contains ·) then
        let ks ← out.get
        unless ks.any (· == K) do out.set (ks.push K)
  -- none whose content depends on the iteration (an inner loop that rewrites the cell from its
  -- start each time): a cell that the left side writes and the expected world does not
  if (← out.get).isEmpty then
    if let some (_, lhs, rhs) := e.consumeMData.eq? then
      Meta.forEachExpr lhs fun sub => do
        if sub.isAppOf ``Std.ExtDHashMap.insert && sub.getAppNumArgs ≥ 2 then
          let K := sub.getArg! (sub.getAppNumArgs - 2)
          if K.isAppOfArity ``Prod.mk 4 && !mentions K && !K.hasLooseBVars &&
              !K.hasAnyFVar (!lctx.contains ·) &&
              !(rhs.find? (fun r => r.isAppOf ``Std.ExtDHashMap.insert && r.getAppNumArgs ≥ 2 &&
                r.getArg! (r.getAppNumArgs - 2) == K)).isSome then
            let ks ← out.get
            unless ks.any (· == K) do out.set (ks.push K)
  out.get

/-- Find the goal with the given tag (without macro scopes) among `gls`. -/
def goalTagged (gls : List MVarId) (n : Name) : TacticM (Option MVarId) := do
  return (← gls.filterM fun g => return (← g.getTag).eraseMacroScopes == n).head?

/-- Close the side goals `hw`/`hw0`/`hcell` of a summary when `simp` can; keep the others. -/
def closeSideGoals (gls : List MVarId) : TacticM Unit := do
  let mut rest := #[]
  for g in gls do
    let tag := (← g.getTag).eraseMacroScopes
    setGoals [g]
    let tac ← if tag == `hw then
        `(tactic| first | assumption | (simp (disch := first | decide | omega) only [ts_sym]; assumption) | (simp (disch := first | decide | omega) only [ts_sym]; rfl) | (simp [ts_sym, *]; done))
      else if tag == `hcell then
        `(tactic| (intro c; first | (simp (disch := first | decide | omega) only [ts_sym]; assumption) | (simp (disch := first | decide | omega) [ts_sym, *]; done)))
      else if tag == `hw0 then
        `(tactic| first
          | rfl
          | (refine World.eq_insert_getD _ _ _ ?_; simp (disch := first | decide | omega) [ts_sym, *]; done)
          | (refine World.eq_insert_of_get? _ _ _ ?_; simp (disch := first | decide | omega) [ts_sym, *]; done)
          | (refine World.eq_insert2_getD _ _ _ _ _ ?_ ?_ <;> simp (disch := first | decide | omega) [ts_sym, *]))
      else `(tactic| skip)
    if tag == `hw || tag == `hcell || tag == `hw0 then
      try evalTactic tac catch _ => pure ()
    rest := rest ++ (← getGoals).toArray
  setGoals rest.toList

/-- Prove `p` with the tactic `tac` in the main goal's context, without logging errors: the proof,
or `none`. -/
def proveProp? (p : Lean.Expr) (tac : TSyntax `tactic) : TacticM (Option Lean.Expr) := withMainContext do
  let g ← mkFreshExprMVar p
  let saved ← saveState
  try
    let rest ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run g.mvarId! (evalTactic tac)
    if rest.isEmpty then
      let pf ← instantiateMVars g
      if pf.hasSyntheticSorry || pf.hasSorry then saved.restore; return none
      return some pf
    saved.restore; return none
  catch _ => saved.restore; return none

/-- Add the hypothesis `nm : p` (proved by `pf`) to the main goal. -/
def addHyp (nm : Name) (p pf : Lean.Expr) : TacticM Unit :=
  liftMetaTactic fun g => do
    let g' ← g.assert nm p pf
    let (_, g'') ← g'.intro1P
    return [g'']

/-- Disequalities between the heap keys in the goal and the hypotheses: addresses that `omega`
proves different (e.g. `w.next ≠ a` from `a < w.next`) and different kinds, as local hypotheses
(`hne_addr_…`, `hne_kind_…`) and as instances of the read-through-write lemmas, so that `simp`
reads a cell through a write or an allocation of another cell. -/
def heapNeFacts : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := withMainContext do
  let mut addrs : Array Lean.Expr := #[]
  let mut kinds : Array Lean.Expr := #[]
  let mut srcs : Array Lean.Expr := #[← instantiateMVars (← getMainTarget)]
  for d in ← getLCtx do
    unless d.isImplementationDetail do srcs := srcs.push (← instantiateMVars d.type)
  let lctx ← getLCtx
  for e in srcs do
    let found ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
    Meta.forEachExpr e fun sub => do
      -- (keys under binders mention the fresh variables `forEachExpr` introduces)
      if sub.isAppOfArity ``Prod.mk 4 && !sub.hasLooseBVars && !sub.hasAnyFVar (!lctx.contains ·) then
        let k := sub.getArg! 2
        if (← whnfR (← inferType k)).isConstOf ``HKind then
          found.modify (·.push (k, sub.getArg! 3))
    for (k, a) in ← found.get do
      unless addrs.any (· == a) do addrs := addrs.push a
      unless kinds.any (· == k) do kinds := kinds.push k
  let mut out := #[]
  let mut kidx := 0
  for i in [0:kinds.size] do
    for j in [0:kinds.size] do
      if i == j then continue
      let p ← mkAppM ``Ne #[kinds[i]!, kinds[j]!]
      let some pf ← proveProp? p (← `(tactic| (intro h; cases h))) | continue
      let nmN := Name.mkSimple s!"hne_kind_{kidx}"
      addHyp nmN p pf
      let nm := mkIdent nmN
      out := out.push (← `(Lean.Parser.Tactic.simpLemma| StrictTS.JS.heap_get_insert_kind_ne _ _ _ _ $nm:ident))
      out := out.push (← `(Lean.Parser.Tactic.simpLemma| StrictTS.heap_insert_shadow_kind _ _ _ _ _ _ $nm:ident))
      kidx := kidx + 1
  let mut idx := 0
  for i in [0:addrs.size] do
    for j in [0:addrs.size] do
      if i == j then continue
      let p ← mkAppM ``Ne #[addrs[i]!, addrs[j]!]
      let some pf ← proveProp? p (← `(tactic| omega)) | continue
      let nmN := Name.mkSimple s!"hne_addr_{idx}"
      addHyp nmN p pf
      let nm := mkIdent nmN
      out := out.push (← `(Lean.Parser.Tactic.simpLemma| $nm:ident))
      out := out.push (← `(Lean.Parser.Tactic.simpLemma| StrictTS.JS.heap_get_insert_addr_ne _ _ _ _ $nm:ident))
      out := out.push (← `(Lean.Parser.Tactic.simpLemma| StrictTS.heap_insert_shadow_addr _ _ _ _ _ _ $nm:ident))
      idx := idx + 1
  return out


/-- Remove the disequalities added by `heapNeFacts` (they were only needed inside a summary). -/
def clearNeFacts : TacticM Unit := do
  -- (a nested summarization leaves them: the enclosing one's lemmas name them)
  if ← Summarize.nested then return
  let names ← withMainContext do
    return (← getLCtx).foldl (init := #[]) fun acc d =>
      let n := d.userName.eraseMacroScopes.toString
      if n.startsWith "hne_addr_" || n.startsWith "hne_kind_" then acc.push d.fvarId else acc
  for fv in names.reverse do
    try liftMetaTactic fun g => do return [← g.clear fv] catch _ => pure ()

/-- How a summarization attempt ended. -/
inductive Attempt where
  | done
  /-- the iteration did not evaluate to one state (goal, iteration variables) -/
  | stuck (g : MVarId) (locals : Array FVarId)
  /-- an iteration may end with something other than going on (`break`, `return`, `throw`) -/
  | notNext

/-- After a loop whose iterations may `return` is rewritten, its completion is
`Completion.ofRet r`. The code after the loop is run for both cases: the term `T` holding the
completion (the left side of an equation, or else the whole goal) becomes `optCase r A B`, with `A`
the result when no iteration returned and `B v` the result after `return v`, and then one value
`r.elim …` where `A` and `B v` agree. -/
def splitRet (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  let main ← getMainGoal
  let some (T, r, el) ← main.withContext do
      let goal ← instantiateMVars (← main.getType)
      let some o := goal.find? (fun e => e.isAppOfArity ``Completion.ofRet 3 && !e.hasLooseBVars)
        | return none
      -- split on the fold's flag itself when the returned value is projected from it (it also
      -- carries the position and the world after the returning iteration)
      let r := o.appArg!
      let r := if r.isAppOfArity ``Option.map 4 then r.appArg! else r
      let rTy ← whnfR (← inferType r)
      unless rTy.isAppOfArity ``Option 1 do return none
      let T := match goal.consumeMData.eq? with
        | some (_, lhs, _) => if (lhs.find? (· == o)).isSome then lhs else goal
        | none => goal
      return some (T, r, rTy.appArg!)
    | return
  -- prove `T = M` in a goal of its own, `M` read off by `rfl`
  let (α, M, g) ← main.withContext do
    let α ← inferType T
    let M ← mkFreshExprMVar α
    return (α, M, ← mkFreshExprMVar (← mkEq T M))
  setGoals [g.mvarId!]
  let (A, B) ← withMainContext do return (← mkFreshExprMVar α, ← mkFreshExprMVar (← mkArrow el α))
  let (rS, AS, BS, MS) ← withMainContext do
    return (← Term.exprToSyntax r, ← Term.exprToSyntax A, ← Term.exprToSyntax B, ← Term.exprToSyntax M)
  let hr := mkIdent (← MonadQuotation.addMacroScope `hr)
  let vI := mkIdent (← MonadQuotation.addMacroScope `v)
  let hyps := (← heapHyps) ++ extra
  evalTactic (← `(tactic| refine Eq.trans (c := $MS) (Merge.split_opt (d := $rS)) ?_))
  evalTactic (← `(tactic|
    refine Eq.trans (c := $MS)
      (Merge.optCase_congr (a' := $AS) (b' := $BS) (fun $hr => ?_) (fun $vI $hr => ?_)) ?_))
  let gls ← getGoals
  -- the two cases: run the code after the loop, read its result off by `rfl`
  for g in gls.take 2 do
    setGoals [g]
    evalTactic (← `(tactic| rewrite [$hr:ident]))
    try evalTactic (← `(tactic|
      simp only [Completion.ofRet_none, Completion.ofRet_some, Option.map_none, Option.map_some,
        Option.getD_none, Option.getD_some, ts_sym, ne_eq, reduceCtorEq, not_false_eq_true,
        Env.get_here', Env.get_there', Env.set_here', Env.set_there', Env.getC_here', Env.getC_there',
        Env.head_cons, Env.tail_cons, $hyps,*]))
    catch _ => pure ()
    evalTactic (← `(tactic| rfl))
  setGoals (gls.drop 2)
  -- one value where the two cases agree (not for a proposition: `simp` evaluates each case)
  let merged ← if α.isProp then pure none else withMainContext do
    let A ← instantiateMVars A
    let B ← instantiateMVars B
    withLocalDeclD `v el fun v => do
      let Bv := (B.beta #[v]).headBeta
      let m ← try antiUnify (fun x y => do mkAppM ``Option.elim #[r, x, ← mkLambdaFVars #[v] y]) A Bv
        catch _ => return none
      if m.containsFVar v.fvarId! then return none
      return some m
  if let some m := merged then
    let mS ← withMainContext <| Term.exprToSyntax m
    evalTactic (← `(tactic| refine Eq.trans (b := $mS) (c := $MS) ?_ ?_))
    let gls ← getGoals
    setGoals [gls.head!]
    evalTactic (← `(tactic| (generalize $rS = om; cases om <;> rfl)))
    setGoals gls.tail!
  evalTactic (← `(tactic| rfl))
  -- replace `T` by `M` in the goal
  let pf ← instantiateMVars g
  let res ← main.withContext do main.rewrite (← instantiateMVars (← main.getType)) pf
  let main' ← main.replaceTargetEq res.eNew res.eqProof
  setGoals (main' :: res.mvarIds)

/-- The rest of a summarization attempt, after `have hsum := <summary theorem> … ?hF ?hC …`:
compute the iteration symbolically in `?hF` (introducing `nIntro` variables), check that every
iteration goes on, or leaves the loop when `brk` (`?hC`) or returns when `ret`, close the side
goals, and rewrite the loop with `hsum` (then, when `ret`, run the code after the loop for both
completions: `splitRet`). -/
def finishSummary (hsum : Ident) (nIntro : Nat) (stepMVars : Array Lean.Expr) (brk : Bool)
    (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) (memb : Bool := false)
    (ret : Bool := false) :
    TacticM Attempt := do
  let gls ← getGoals
  let some hF ← goalTagged gls `hF | throwError "ts_summarize: internal error (no hF goal)"
  let mut hyps := (← heapHyps) ++ extra
  setGoals [hF]
  -- hygienic names: the user's extra lemmas may mention variables called `x`, `s` or `c`
  let names := #[mkIdent (← MonadQuotation.addMacroScope `x), mkIdent (← MonadQuotation.addMacroScope `s),
    mkIdent (← MonadQuotation.addMacroScope `c)].extract 0 nIntro
  -- for a string loop the iteration also gets `x ∈ cps` (a simp fact for the body)
  if memb then
    let hm := mkIdent (← MonadQuotation.addMacroScope `hmem)
    let rest := names.extract 1 nIntro
    evalTactic (← `(tactic| intro x $hm:ident $rest*))
    hyps := hyps.push (← `(Lean.Parser.Tactic.simpLemma| $hm:ident))
  else
    evalTactic (← `(tactic| intro $names*))
  let locals ← withMainContext do
    let lctx ← getLCtx
    return (lctx.getFVarIds.toList.reverse.take (if memb then nIntro + 1 else nIntro)).toArray
  evalTactic (← `(tactic| ts_merge [$hyps,*]))
  unless (← getGoals).isEmpty do
    return .stuck (← getMainGoal) locals
  for g in stepMVars do
    unless ← g.mvarId!.isAssigned do
      throwError "ts_summarize: could not read off the step function"
  let gls := gls.filter (· != hF)
  let some hC ← goalTagged gls `hC | throwError "ts_summarize: internal error (no hC goal)"
  setGoals [hC]
  try
    if brk then evalTactic (← `(tactic| (intro $names*; simp [Completion.isNextOrBrk_ite, iteStaleInstance])))
    else if ret then evalTactic (← `(tactic| (intro $names*; simp [Completion.isNextOrRet_ite, iteStaleInstance])))
    else evalTactic (← `(tactic| (intro $names*; simp [Completion.isNext_ite, iteStaleInstance])))
  catch _ => return .notNext
  unless (← getGoals).isEmpty do return .notNext
  -- side goals first (solving the array cell assigns `xs` when it was not given)
  let rest := gls.filter (· != hC)
  let main := rest.head!
  closeSideGoals rest.tail!
  let side ← getGoals
  setGoals [main]
  evalTactic (← `(tactic| rw [$hsum:ident]))
  -- (the rewrite may close the goal: both sides summarized to the same fold)
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| clear $hsum:ident))
  if ret && !(← getGoals).isEmpty then splitRet extra
  unless (← getGoals).isEmpty do clearNeFacts
  setGoals ((← getGoals) ++ side)
  return .done

/-- One summarization attempt: world unchanged (`cell = none`) or cell `K` written. Returns
`none` on success, or the iteration's symbolic result goal (for diagnosis) on failure. -/
def summarizeAttempt (xs? : Option Term) (cell : Option Lean.Expr) (brk : Bool)
    (extra0 : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) (cell2 : Option Lean.Expr := none)
    (ret : Bool := false) :
    TacticM Attempt := do
  let extra := (← heapNeFacts) ++ extra0
  withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalForOf)
    | throwError "ts_summarize: no `for … of` loop (evalForOf) in the goal"
  let loop := e.getArg! 2
  let w0 := e.getArg! 3
  let args := loop.getAppArgs
  -- evalForOf {TT} I P {Γ} {ρ} {t} a i body env
  let TT := args[0]!
  let Γ := args[3]!
  let ρ := args[4]!
  let t := args[5]!
  let env0 := args[9]!
  let spine ← ctxSpine Γ
  let mut isMut : Array Bool := #[]
  let mut tys : Array Lean.Expr := #[]
  for (s, _) in spine do
    let m ← whnf (mkApp (mkConst ``Slot.mutable) s)
    isMut := isMut.push (m.isConstOf ``Bool.true)
    tys := tys.push (← whnf (mkApp (mkConst ``Slot.ty) s))
  let comps ← envComps env0 spine.size
  let mutIdx0 := (List.range spine.size).filter (fun i => isMut[i]!)
  -- (mutable variables that the body never assigns keep their values: not part of the state)
  let assigned? ← assignedSlots #[(args[8]!, 1)]
  let mutIdx := mutIdx0.filter (fun i => assigned?.all (·.contains i))
  let valTys := mutIdx.map (fun i => mkApp2 (mkConst ``Val) TT tys[i]!)
  let σ ← mkProdTy valTys
  let m := mutIdx.length
  let enc ← withLocalDeclD `s σ fun s => do
    let ps ← tupleProjs s m
    mkLambdaFVars #[s] (← mkEnvLit TT spine isMut comps (mutVals mutIdx0 mutIdx comps ps.toArray none))
  let s0 ← mkTuple (mutIdx.map (fun i => comps[i]!))
  let xT := mkApp2 (mkConst ``Val) TT t
  let compT := mkApp2 (mkConst ``Completion) TT ρ
  -- the extra state: the written cell's content (or the pair of the two cells' contents)
  let kindOf (K : Lean.Expr) : TacticM Lean.Expr := do
    if K.isAppOfArity ``Prod.mk 4 then pure (K.getArg! 2) else mkAppM ``Prod.fst #[K]
  let kind? ← cell.mapM kindOf
  let κ1? ← kind?.mapM fun kind => whnfR (mkApp2 (mkConst ``HKind.Cell) TT kind)
  let kind2? ← cell2.mapM kindOf
  let κ2? ← kind2?.mapM fun kind => whnfR (mkApp2 (mkConst ``HKind.Cell) TT kind)
  let κ? ← match κ1?, κ2? with
    | some κ1, some κ2 => some <$> mkAppM ``Prod #[κ1, κ2]
    | κ1?, _ => pure κ1?
  let arrows (res : Lean.Expr) : MetaM Lean.Expr := do
    match κ? with
    | none => mkArrow xT (← mkArrow σ res)
    | some κ => mkArrow xT (← mkArrow σ (← mkArrow κ res))
  -- one metavariable per mutable slot (its value after one iteration), the completion, the cell(s)
  let mut gs : Array Lean.Expr := #[]
  for vt in valTys do
    gs := gs.push (← mkFreshExprMVar (← arrows vt))
  let C ← mkFreshExprMVar (← arrows compT)
  -- the cells' new contents: one metavariable per cell, paired for two cells
  let Hs ← match κ1?, κ2? with
    | some κ1, some κ2 => pure #[← mkFreshExprMVar (← arrows κ1), ← mkFreshExprMVar (← arrows κ2)]
    | some _, none => do
      let some κ := κ? | pure #[]
      pure #[← mkFreshExprMVar (← arrows κ)]
    | _, _ => pure #[]
  let H? ← match κ? with
    | none => pure none
    | some κ =>
      if Hs.size == 2 then
        some <$> (withLocalDeclD `x xT fun x => withLocalDeclD `s σ fun s => withLocalDeclD `c κ fun c => do
          mkLambdaFVars #[x, s, c] (← mkAppM ``Prod.mk #[mkApp3 Hs[0]! x s c, mkApp3 Hs[1]! x s c]))
      else pure Hs[0]?
  let G ← withLocalDeclD `x xT fun x => withLocalDeclD `s σ fun s => do
    match κ? with
    | none => mkLambdaFVars #[x, s] (← mkTuple (gs.toList.map (fun g => mkApp2 g x s)))
    | some κ => withLocalDeclD `c κ fun c => do
      mkLambdaFVars #[x, s, c] (← mkTuple (gs.toList.map (fun g => mkApp3 g x s c)))
  let I ← Term.exprToSyntax args[1]!
  let P ← Term.exprToSyntax args[2]!
  let a ← Term.exprToSyntax args[6]!
  let body ← Term.exprToSyntax args[8]!
  let xs ← match xs? with
    | some xs => pure xs
    | none => do Term.exprToSyntax (← mkFreshExprMVar (mkApp (mkConst ``Array [0]) xT))
  let encS ← Term.exprToSyntax enc
  let GS ← Term.exprToSyntax G
  let CS ← Term.exprToSyntax C
  let s0S ← Term.exprToSyntax s0
  let envS ← Term.exprToSyntax env0
  let wS ← Term.exprToSyntax w0
  let hsum := mkIdent `hsum
  let henv ← `(by first | rfl | simp only [Env.cons_head_tail])
  match cell, κ?, H?, kind? with
  | some K, some κ, some H, some kind =>
    let KS ← Term.exprToSyntax K
    let κS ← Term.exprToSyntax κ
    let kindS ← Term.exprToSyntax kind
    -- the world of an iteration with the cell(s) holding `c`, and the cells' contents at the loop
    let (putS, c0S) ← match cell2, kind2? with
      | some K2, some kind2 => do
        let K2S ← Term.exprToSyntax K2
        let kind2S ← Term.exprToSyntax kind2
        pure (← `(fun c => { $wS with
                  heap := (Std.ExtDHashMap.insert (Std.ExtDHashMap.insert (World.heap $wS) $KS c.1) $K2S c.2) }),
          ← `(((Std.ExtDHashMap.get? (World.heap $wS) $KS).getD (HKind.dflt $kindS),
                (Std.ExtDHashMap.get? (World.heap $wS) $K2S).getD (HKind.dflt $kind2S))))
      | _, _ => do
        pure (← `(fun c => { $wS with heap := Std.ExtDHashMap.insert (World.heap $wS) $KS c }),
          ← `((Std.ExtDHashMap.get? (World.heap $wS) $KS).getD (HKind.dflt $kindS)))
    if m == 0 && !brk && !ret then
      -- no mutable variable: the fold is over the cells' contents alone
      let C1 ← mkFreshExprMVar (← mkArrow xT (← mkArrow κ compT))
      let (H1, H1s) ← match κ1?, κ2? with
        | some κ1, some κ2 => do
          let ha ← mkFreshExprMVar (← mkArrow xT (← mkArrow κ κ1))
          let hb ← mkFreshExprMVar (← mkArrow xT (← mkArrow κ κ2))
          let lam ← withLocalDeclD `x xT fun x => withLocalDeclD `c κ fun c => do
            mkLambdaFVars #[x, c] (← mkAppM ``Prod.mk #[mkApp2 ha x c, mkApp2 hb x c])
          pure (lam, #[ha, hb])
        | _, _ => do
          let h1 ← mkFreshExprMVar (← mkArrow xT (← mkArrow κ κ))
          pure (h1, #[h1])
      let C1S ← Term.exprToSyntax C1
      let H1S ← Term.exprToSyntax H1
      evalTactic (← `(tactic|
        have $hsum := StrictTS.evalForOf_summary_cell1 $I $P $body $a $xs (κ := $κS) $envS
          $putS $C1S $H1S $c0S $wS ?hw0 ?hcell ?hF ?hC))
      finishSummary hsum 2 (#[C1] ++ H1s) brk extra
    else
      let HS ← Term.exprToSyntax H
      let thm := mkIdent (if brk then ``StrictTS.evalForOf_summary_cells_brk
        else if ret then ``StrictTS.evalForOf_summary_cells_ret else ``StrictTS.evalForOf_summary_cells)
      evalTactic (← `(tactic|
        have $hsum := $thm $I $P $body $a $xs (κ := $κS) $encS
          $putS $CS $GS $HS $s0S $c0S $envS $henv $wS ?hw0 ?hcell ?hF ?hC))
      finishSummary hsum 3 ((gs.push C) ++ Hs) brk extra (ret := ret)
  | _, _, _, _ =>
    let thm := mkIdent (if brk then ``StrictTS.evalForOf_summary_pure_brk
      else if ret then ``StrictTS.evalForOf_summary_pure_ret else ``StrictTS.evalForOf_summary_pure)
    evalTactic (← `(tactic|
      have $hsum := $thm $I $P $body $a $xs $encS $CS $GS $s0S $envS $henv
        $wS ?hw ?hF ?hC))
    finishSummary hsum 2 (gs.push C) brk extra (ret := ret)

/-- The loops over the code points of a string, the entries of a `Map` and the elements of a
`Set` (iterated live; summarized when the body leaves the map or set unchanged). -/
inductive LiveKind where
  | str | map | set

/-- One summarization attempt for a `for … of` loop over a string, map or set: world unchanged
(`cell = none`) or cell `K` written. -/
def summarizeLiveAttempt (kind : LiveKind) (cell : Option Lean.Expr)
    (extra0 : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) (brk : Bool := false) (ret : Bool := false) :
    TacticM Attempt := do
  let extra := (← heapNeFacts) ++ extra0
  withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let fn := match kind with
    | .str => ``evalForOfStr | .map => ``evalForOfMap | .set => ``evalForOfSet
  let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf fn)
    | throwError "ts_summarize: internal error (loop not found)"
  let loop := e.getArg! 2
  let w0 := e.getArg! 3
  let args := loop.getAppArgs
  let TT := args[0]!
  let Γ := args[3]!
  let ρ := args[4]!
  -- the iteration variable's type, the body, the environment, and the iterated container
  let (elT, bodyE, envE, aE?, cont?) ← match kind with
    | .str => pure (mkConst ``JSStr, args[6]!, args[7]!, none, none)
    | .map => do
      let k := args[5]!
      let v := args[6]!
      let tupT := mkApp (mkConst ``Ty.tup) (mkApp2 (mkConst ``Tys.cons) k (mkApp2 (mkConst ``Tys.cons) v (mkConst ``Tys.nil)))
      let mT := mkApp2 (mkConst ``JSMap) (mkApp2 (mkConst ``Val) TT k) (mkApp2 (mkConst ``Val) TT v)
      pure (mkApp2 (mkConst ``Val) TT tupT, args[9]!, args[10]!, some args[7]!, some (← mkFreshExprMVar mT))
    | .set => do
      let t := args[5]!
      let mT := mkApp2 (mkConst ``JSMap) (mkApp2 (mkConst ``Val) TT t) (mkConst ``Unit)
      pure (mkApp2 (mkConst ``Val) TT t, args[8]!, args[9]!, some args[6]!, some (← mkFreshExprMVar mT))
  let spine ← Summarize.ctxSpine Γ
  let mut isMut : Array Bool := #[]
  let mut tys : Array Lean.Expr := #[]
  for (sl, _) in spine do
    let m ← whnf (mkApp (mkConst ``Slot.mutable) sl)
    isMut := isMut.push (m.isConstOf ``Bool.true)
    tys := tys.push (← whnf (mkApp (mkConst ``Slot.ty) sl))
  let comps ← Summarize.envComps envE spine.size
  let mutIdx0 := (List.range spine.size).filter (fun i => isMut[i]!)
  -- (mutable variables that the body never assigns keep their values: not part of the state)
  let assigned? ← Summarize.assignedSlots #[(bodyE, 1)]
  let mutIdx := mutIdx0.filter (fun i => assigned?.all (·.contains i))
  let valTys := mutIdx.map (fun i => mkApp2 (mkConst ``Val) TT tys[i]!)
  let σ ← Summarize.mkProdTy valTys
  let m := mutIdx.length
  let enc ← withLocalDeclD `s σ fun s => do
    let ps ← Summarize.tupleProjs s m
    mkLambdaFVars #[s] (← Summarize.mkEnvLit TT spine isMut comps
      (Summarize.mutVals mutIdx0 mutIdx comps ps.toArray none))
  let s0 ← Summarize.mkTuple (mutIdx.map (fun i => comps[i]!))
  let compT := mkApp2 (mkConst ``Completion) TT ρ
  let kind? ← cell.mapM fun K => do
    if K.isAppOfArity ``Prod.mk 4 then pure (K.getArg! 2) else mkAppM ``Prod.fst #[K]
  let κ? ← kind?.mapM fun kd => whnfR (mkApp2 (mkConst ``HKind.Cell) TT kd)
  let arrows (res : Lean.Expr) : MetaM Lean.Expr := do
    match κ? with
    | none => mkArrow elT (← mkArrow σ res)
    | some κ => mkArrow elT (← mkArrow σ (← mkArrow κ res))
  let mut gs : Array Lean.Expr := #[]
  for vt in valTys do
    gs := gs.push (← mkFreshExprMVar (← arrows vt))
  let C ← mkFreshExprMVar (← arrows compT)
  let H? ← κ?.mapM fun κ => do mkFreshExprMVar (← arrows κ)
  let G ← withLocalDeclD `x elT fun x => withLocalDeclD `s σ fun s => do
    match κ? with
    | none => mkLambdaFVars #[x, s] (← Summarize.mkTuple (gs.toList.map (fun g => mkApp2 g x s)))
    | some κ => withLocalDeclD `c κ fun c => do
      mkLambdaFVars #[x, s, c] (← Summarize.mkTuple (gs.toList.map (fun g => mkApp3 g x s c)))
  let I ← Term.exprToSyntax args[1]!
  let P ← Term.exprToSyntax args[2]!
  let bodyS ← Term.exprToSyntax bodyE
  let encS ← Term.exprToSyntax enc
  let GS ← Term.exprToSyntax G
  let CS ← Term.exprToSyntax C
  let s0S ← Term.exprToSyntax s0
  let envS ← Term.exprToSyntax envE
  let wS ← Term.exprToSyntax w0
  let hsum := mkIdent `hsum
  let henv ← `(by first | rfl | simp only [Env.cons_head_tail])
  -- the arguments between `body` and `enc`: the code points, or the address and the container
  let mid : Array Term ← match kind, aE?, cont? with
    | .str, _, _ => pure #[← Term.exprToSyntax args[5]!]
    | _, some aE, some cont => pure #[← Term.exprToSyntax aE, ← Term.exprToSyntax cont]
    | _, _, _ => throwError "ts_summarize: internal error (no container)"
  let memb := match kind with | .str => true | _ => false
  if brk || ret then
    -- with `break` or `return`: the versions with a cell (`κ = Unit` when the world is unchanged)
    let (κS, putS, c0S, HS, Hs) ← match cell, κ?, H?, kind? with
      | some K, some κ, some H, some kd => do
        let KS ← Term.exprToSyntax K
        let kdS ← Term.exprToSyntax kd
        pure (← Term.exprToSyntax κ,
          ← `(fun c => { $wS with heap := Std.ExtDHashMap.insert (World.heap $wS) $KS c }),
          ← `((Std.ExtDHashMap.get? (World.heap $wS) $KS).getD (HKind.dflt $kdS)),
          ← Term.exprToSyntax H, #[H])
      | _, _, _, _ => do
        pure (← `(Unit), ← `(fun (_ : Unit) => $wS), ← `(()), ← `(fun _ _ _ => ()), #[])
    -- the iteration functions take the world's part as a third argument
    let (GS3, CS3, gs3, C3) ← if cell.isSome then pure (GS, CS, gs, C) else do
      let C3 ← mkFreshExprMVar (← mkArrow elT (← mkArrow σ (← mkArrow (mkConst ``Unit) compT)))
      let mut gs3 : Array Lean.Expr := #[]
      for vt in valTys do
        gs3 := gs3.push (← mkFreshExprMVar (← mkArrow elT (← mkArrow σ (← mkArrow (mkConst ``Unit) vt))))
      let G3 ← withLocalDeclD `x elT fun x => withLocalDeclD `s σ fun s => withLocalDeclD `c (mkConst ``Unit) fun c => do
        mkLambdaFVars #[x, s, c] (← Summarize.mkTuple (gs3.toList.map (fun g => mkApp3 g x s c)))
      pure (← Term.exprToSyntax G3, ← Term.exprToSyntax C3, gs3, C3)
    let suffix := if brk then "brk" else "ret"
    let thm := mkIdent <| match kind with
      | .str => Name.mkStr `StrictTS s!"evalForOfStr_summary_cells_{suffix}"
      | .map => Name.mkStr `StrictTS s!"evalForOfMap_summary_cells_{suffix}"
      | .set => Name.mkStr `StrictTS s!"evalForOfSet_summary_cells_{suffix}"
    match kind with
    | .str =>
      evalTactic (← `(tactic| have $hsum := $thm $I $P $bodyS $(mid[0]!)
        (κ := $κS) $encS $putS $CS3 $GS3 $HS $s0S $c0S $envS $henv $wS ?hw0 ?hF ?hC))
    | _ =>
      evalTactic (← `(tactic| have $hsum := $thm $I $P $bodyS $(mid[0]!) $(mid[1]!)
        (κ := $κS) $encS $putS $CS3 $GS3 $HS $s0S $c0S $envS $henv $wS ?hw0 ?hcell ?hF ?hC))
    return ← finishSummary hsum 3 ((gs3.push C3) ++ Hs) brk extra memb (ret := ret)
  match cell, κ?, H?, kind? with
  | some K, some κ, some H, some kd =>
    let KS ← Term.exprToSyntax K
    let κS ← Term.exprToSyntax κ
    let kdS ← Term.exprToSyntax kd
    let HS ← Term.exprToSyntax H
    let putS ← `(fun c => { $wS with heap := Std.ExtDHashMap.insert (World.heap $wS) $KS c })
    let c0S ← `((Std.ExtDHashMap.get? (World.heap $wS) $KS).getD (HKind.dflt $kdS))
    match kind with
    | .str =>
      evalTactic (← `(tactic| have $hsum := StrictTS.evalForOfStr_summary_cells $I $P $bodyS $(mid[0]!)
        (κ := $κS) $encS $putS $CS $GS $HS $s0S $c0S $envS $henv $wS ?hw0 ?hF ?hC))
    | .map =>
      evalTactic (← `(tactic| have $hsum := StrictTS.evalForOfMap_summary_cells $I $P $bodyS $(mid[0]!) $(mid[1]!)
        (κ := $κS) $encS $putS $CS $GS $HS $s0S $c0S $envS $henv $wS ?hw0 ?hcell ?hF ?hC))
    | .set =>
      evalTactic (← `(tactic| have $hsum := StrictTS.evalForOfSet_summary_cells $I $P $bodyS $(mid[0]!) $(mid[1]!)
        (κ := $κS) $encS $putS $CS $GS $HS $s0S $c0S $envS $henv $wS ?hw0 ?hcell ?hF ?hC))
    finishSummary hsum 3 ((gs.push C).push H) false extra memb
  | _, _, _, _ =>
    match kind with
    | .str =>
      evalTactic (← `(tactic| have $hsum := StrictTS.evalForOfStr_summary_pure $I $P $bodyS $(mid[0]!)
        $encS $CS $GS $s0S $envS $henv $wS ?hF ?hC))
    | .map =>
      evalTactic (← `(tactic| have $hsum := StrictTS.evalForOfMap_summary_pure $I $P $bodyS $(mid[0]!) $(mid[1]!)
        $encS $CS $GS $s0S $envS $henv $wS ?hw ?hF ?hC))
    | .set =>
      evalTactic (← `(tactic| have $hsum := StrictTS.evalForOfSet_summary_pure $I $P $bodyS $(mid[0]!) $(mid[1]!)
        $encS $CS $GS $s0S $envS $henv $wS ?hw ?hF ?hC))
    finishSummary hsum 2 (gs.push C) false extra memb

/-! Counted loops (`for (let i = k0; i < n; i++)`). -/

/-- The position of a variable in its context (`here` = 0, `there v` = 1 + position of `v`). -/
partial def Summarize.varPos (e : Lean.Expr) : MetaM (Option Nat) := do
  let e ← whnfR e
  if e.isAppOf ``Var.here || e.isAppOf ``MVar.here then return some 0
  if e.isAppOf ``Var.there || e.isAppOf ``MVar.there then
    return (← Summarize.varPos e.appArg!).map (· + 1)
  return none

/-- The counter of a counted loop: the slot that its step block (`i = i + 1`) assigns. -/
def Summarize.counterSlot (step : Lean.Expr) : MetaM (Option Nat) := do
  let st ← whnfR step
  unless st.isAppOfArity ``Block.seq 5 do return none
  let s ← whnfR (st.getArg! 3)
  unless s.isAppOfArity ``Stmt.assign 6 do return none
  Summarize.varPos (s.getArg! 4)

/-- The summary theorem used for a counted loop. -/
inductive CountShape where
  /-- world unchanged -/
  | pure
  /-- one cell written, other mutable variables -/
  | cells
  /-- one cell written, no other mutable variable -/
  | cell1

/-- The condition of a forward counted loop (`?hcond`, the main goal): read its value off, choose
the bound `n` (`i < e`, `i < a - c`, `i <= e`, `i <= a - c` are `i < n'`) and rewrite the condition
to `i < n`. `nIntro` names the binders before the two bound hypotheses (`k s`, `k s c` or `k c`). -/
def readCountedBound (nIntro : Nat) (nM : Lean.Expr) (hyps : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM Unit := do
  let shape : CountShape := if nIntro == 3 then .cells else .pure
  let kI := mkIdent (← MonadQuotation.addMacroScope `k)
  let hk0I := mkIdent (← MonadQuotation.addMacroScope `hk0)
  let hkI := mkIdent (← MonadQuotation.addMacroScope `hk)
  match shape with
  | .pure => evalTactic (← `(tactic| intro $kI:ident s $hk0I:ident $hkI:ident))
  | .cells => evalTactic (← `(tactic| intro $kI:ident s c $hk0I:ident $hkI:ident))
  | .cell1 => evalTactic (← `(tactic| intro $kI:ident c $hk0I:ident $hkI:ident))
  -- read the condition's value off first (`?V`), then choose the bound: `i < e`, `i < a - c`,
  -- `i <= e`, `i <= a - c` are `i < n'`; when the start `k0` may exceed `n'`, `n = max k0 n'`
  let (VS, V) ← withMainContext do
    let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
    let some (α, _, _) := tgt.eq? | throwError "ts_summarize: internal error (hcond)"
    let V ← mkFreshExprMVar α
    return (← Term.exprToSyntax V, V)
  evalTactic (← `(tactic| refine Eq.trans (b := $VS) ?_ ?_))
  evalTactic (← `(tactic| ts_merge [F64.lit_eq_ofNat, $hyps,*]))
  unless (← getGoals).length == 1 do
    throwError "ts_summarize: the loop's condition does not evaluate on a symbolic state"
  -- raw literals (left by `F64.lit_eq_ofNat`) are atoms for `omega`
  let fixLit (e : Lean.Expr) : Lean.Expr := match e with
    | .lit (.natVal v) => mkNatLit v
    | e => e
  let some (n', eqn?) ← withMainContext do
      let v := (← instantiateMVars V).consumeMData
      let some b := (v.find? fun e => e.isAppOfArity ``F64.lt 2 || e.isAppOfArity ``F64.le 2) | return none
      unless (b.getArg! 0).isAppOfArity ``F64.ofNat 1 do return none
      let E := b.getArg! 1
      let isSub := E.isAppOfArity ``HSub.hSub 6 && (E.getArg! 4).isAppOfArity ``F64.ofNat 1 &&
        (E.getArg! 5).isAppOfArity ``F64.ofNat 1
      if b.isAppOfArity ``F64.lt 2 && E.isAppOfArity ``F64.ofNat 1 then
        return some (fixLit E.appArg!, none)
      else if b.isAppOfArity ``F64.lt 2 && isSub then
        return some (← mkAppM ``HSub.hSub #[(fixLit (E.getArg! 4).appArg!), (fixLit (E.getArg! 5).appArg!)],
          some ``lt_ofNat_sub_ofNat_eq)
      else if b.isAppOfArity ``F64.le 2 && isSub then
        let c := fixLit (E.getArg! 5).appArg!
        -- `i <= a - 1` is `i < a`
        if c == mkNatLit 1 then
          return some (fixLit (E.getArg! 4).appArg!, some ``le_ofNat_sub_one_eq)
        return some (← mkAppM ``HSub.hSub #[← mkAppM ``HAdd.hAdd #[(fixLit (E.getArg! 4).appArg!), mkNatLit 1],
          c], some ``le_ofNat_sub_ofNat_eq)
      else if b.isAppOfArity ``F64.le 2 && E.isAppOfArity ``F64.ofNat 1 then
        return some (← mkAppM ``HAdd.hAdd #[fixLit E.appArg!, mkNatLit 1], some ``le_ofNat_eq_lt_succ)
      else return none
    | throwError "ts_summarize: the loop's condition is not `i < n` or `i <= n` with `n` fixed (an array \
        length or a constant); remaining goal:\n{← ppGoal (← getMainGoal)}"
  -- (a start above the bound is handled by the summary theorems: the counter ends at `max k0 n`)
  unless ← isDefEq nM n' do throwError "ts_summarize: could not read off the loop's bound"
  let hk2I := mkIdent (← MonadQuotation.addMacroScope `hk2)
  try
    evalTactic (← `(tactic| have $hk2I:ident : $kI:ident ≤ 2 ^ 53 := by omega))
    match eqn? with
    | some eqn =>
      let eqnI := mkIdent eqn
      if eqn == ``le_ofNat_eq_lt_succ || eqn == ``le_ofNat_sub_one_eq then
        evalTactic (← `(tactic| rw [$eqnI:ident $hk2I:ident (by omega)]))
      else
        evalTactic (← `(tactic| rw [$eqnI:ident $hk2I:ident (by omega) (by omega)]))
    | none => pure ()
  catch _ => pure ()
  unless (← getGoals).isEmpty do
    try evalTactic (← `(tactic| rfl)) catch _ => evalTactic (← `(tactic| ts_merge [F64.lit_eq_ofNat, $hyps,*]))
  unless (← getGoals).isEmpty do
    throwError "ts_summarize: the loop's condition is not `i < n` with `n` fixed (an array length or a \
      constant); remaining goal:\n{← ppGoal (← getMainGoal)}"

/-- One summarization attempt for a counted loop (`evalLoop`): world unchanged (`cell = none`)
or cell `K` written. -/
def summarizeCountedAttempt (cell : Option Lean.Expr)
    (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) (ret : Bool := false) (brk : Bool := false)
    (sized : Bool := false) :
    TacticM Attempt := do
  let sizedLem ← `(Lean.Parser.Tactic.simpLemma| StrictTS.sized_size)
  let neFacts := (← heapNeFacts) ++ extra ++ (if sized then #[sizedLem] else #[])
  withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop)
    | throwError "ts_summarize: no loop (evalForOf/evalLoop) in the goal"
  let loop := e.getArg! 2
  let w0 := e.getArg! 3
  let args := loop.getAppArgs
  -- evalLoop {TT} I P {Γ} {ρ} c body step env
  let TT := args[0]!
  let Γ := args[3]!
  let ρ := args[4]!
  let env0 := args[8]!
  let some j ← Summarize.counterSlot args[7]!
    | throwError "ts_summarize: the loop's step is not an assignment of a counter (`i = i + 1`)"
  let spine ← Summarize.ctxSpine Γ
  let mut isMut : Array Bool := #[]
  let mut tys : Array Lean.Expr := #[]
  for (sl, _) in spine do
    let m ← whnf (mkApp (mkConst ``Slot.mutable) sl)
    isMut := isMut.push (m.isConstOf ``Bool.true)
    tys := tys.push (← whnf (mkApp (mkConst ``Slot.ty) sl))
  unless j < spine.size && isMut[j]! && tys[j]!.isConstOf ``Ty.num do
    throwError "ts_summarize: the loop's counter is not a mutable `number` variable"
  let comps ← Summarize.envComps env0 spine.size
  let mutIdx := (List.range spine.size).filter (fun i => isMut[i]!)
  -- (mutable variables that the loop never assigns keep their values: not part of the state)
  let assigned? ← Summarize.assignedSlots #[(args[6]!, 0), (args[7]!, 0)]
  let others := mutIdx.filter (fun i => i != j && assigned?.all (·.contains i))
  let valTys := others.map (fun i => mkApp2 (mkConst ``Val) TT tys[i]!)
  let σ ← Summarize.mkProdTy valTys
  let m := others.length
  let natT := mkConst ``Nat
  let enc ← withLocalDeclD `k natT fun k => withLocalDeclD `s σ fun s => do
    let ps ← Summarize.tupleProjs s m
    let cnt := mkApp2 (mkConst ``Val.num) TT (← mkAppM ``F64.ofNat #[k])
    let mut muts : Array Lean.Expr := #[]
    let mut q := 0
    for i in mutIdx do
      if i == j then muts := muts.push cnt
      else if others.contains i then
        muts := muts.push ps[q]!
        q := q + 1
      else muts := muts.push comps[i]!
    mkLambdaFVars #[k, s] (← Summarize.mkEnvLit TT spine isMut comps muts.toList)
  let s0 ← Summarize.mkTuple (others.map (fun i => comps[i]!))
  let nM ← mkFreshExprMVar natT
  -- the start: read off the counter's initial value when it is a literal (a raw literal from
  -- unification would be an atom for `omega`), else left to unification
  let k0M ← do
    let cv ← whnfR comps[j]!
    let x0 := if cv.isAppOf ``Val.num then cv.appArg! else cv
    if x0.isAppOfArity ``OfNat.ofNat 3 then
      match x0.getArg! 1 with
      | .lit (.natVal v) => pure (mkNatLit v)
      | _ => mkFreshExprMVar natT
    else if x0.isAppOfArity ``F64.ofNat 1 then
      match x0.appArg! with
      | .lit (.natVal v) => pure (mkNatLit v)
      | e => pure e
    else mkFreshExprMVar natT
  let finT := mkApp (mkConst ``Fin) nM
  let compT := mkApp2 (mkConst ``Completion) TT ρ
  let kind? ← cell.mapM fun K => do
    if K.isAppOfArity ``Prod.mk 4 then pure (K.getArg! 2) else mkAppM ``Prod.fst #[K]
  let κ0? ← kind?.mapM fun kind => whnfR (mkApp2 (mkConst ``HKind.Cell) TT kind)
  -- with `sized`, an array cell's content is a state of fixed size `m0` (its start's size)
  let sizedInfo? ← if !sized then pure none else do
    let (some K, some kind, some cellT) := (cell, kind?, κ0?) | pure none
    let kd ← whnfR kind
    if !(kd.isAppOf ``HKind.arr && K.isAppOfArity ``Prod.mk 4) then pure none
    else
      let wS ← Term.exprToSyntax w0
      let KS ← Term.exprToSyntax K
      let kindS ← Term.exprToSyntax kind
      -- the content at the start, evaluated (`xs` from a hypothesis, `c.1` inside an enclosing
      -- loop), else as a lookup
      let X ← mkFreshExprMVar cellT
      let XS ← Term.exprToSyntax X
      let hyps := (← heapHyps) ++ extra
      let g ← mkFreshExprMVar (← Tactic.elabTerm (← `(Std.ExtDHashMap.get? (World.heap $wS) $KS = some $XS))
        (some (mkSort .zero)))
      let saved ← saveState
      let gs ← getGoals
      setGoals [g.mvarId!]
      let ok ← try
          evalTactic (← `(tactic| (simp only [ts_sym, $hyps,*]; rfl)))
          pure ((← getGoals).isEmpty && (← X.mvarId!.isAssigned))
        catch _ => pure false
      setGoals gs
      let c0 ← if ok then instantiateMVars X else do
        saved.restore
        instantiateMVars (← Tactic.elabTerm
          (← `((Std.ExtDHashMap.get? (World.heap $wS) $KS).getD (HKind.dflt $kindS))) (some cellT))
      let m0 ← mkAppM ``Array.size #[c0]
      let κs ← withLocalDeclD `c cellT fun c => do
        mkAppM ``Subtype #[← mkLambdaFVars #[c] (← mkEq (← mkAppM ``Array.size #[c]) m0)]
      pure (some (kd.appArg!, K.getArg! 3, c0, m0, κs, cellT))
  if sized && sizedInfo?.isNone then
    throwError "ts_summarize: the written cell is not an array (fixed-size summary)"
  let κ? := match sizedInfo? with
    | some (_, _, _, _, κs, _) => some κs
    | none => κ0?
  let arrows (res : Lean.Expr) : MetaM Lean.Expr := do
    match κ? with
    | none => mkArrow finT (← mkArrow σ res)
    | some κ => mkArrow finT (← mkArrow σ (← mkArrow κ res))
  let mut gs : Array Lean.Expr := #[]
  for vt in valTys do
    gs := gs.push (← mkFreshExprMVar (← arrows vt))
  let C ← mkFreshExprMVar (← arrows compT)
  -- (with `sized`, the cell's new content is an array, its size an obligation `hH`)
  let H? ← κ?.mapM fun κ => do
    match sizedInfo? with
    | some (_, _, _, _, _, cellT) => mkFreshExprMVar (← arrows cellT)
    | none => mkFreshExprMVar (← arrows κ)
  let G ← withLocalDeclD `i finT fun i => withLocalDeclD `s σ fun s => do
    match κ? with
    | none => mkLambdaFVars #[i, s] (← Summarize.mkTuple (gs.toList.map (fun g => mkApp2 g i s)))
    | some κ => withLocalDeclD `c κ fun c => do
      mkLambdaFVars #[i, s, c] (← Summarize.mkTuple (gs.toList.map (fun g => mkApp3 g i s c)))
  let I ← Term.exprToSyntax args[1]!
  let P ← Term.exprToSyntax args[2]!
  let condS ← Term.exprToSyntax args[5]!
  let bodyS ← Term.exprToSyntax args[6]!
  let stepS ← Term.exprToSyntax args[7]!
  let encS ← Term.exprToSyntax enc
  let GS ← Term.exprToSyntax G
  let CS ← Term.exprToSyntax C
  let nS ← Term.exprToSyntax nM
  let k0S ← Term.exprToSyntax k0M
  let s0S ← Term.exprToSyntax s0
  let envS ← Term.exprToSyntax env0
  let wS ← Term.exprToSyntax w0
  let hsum := mkIdent `hsum
  let henv ← `(by first | rfl | simp only [Env.cons_head_tail])
  if let (some (t, a, c0, m0, _, _), some H) := (sizedInfo?, H?) then
    if ret || brk then throwError "ts_summarize: fixed-size cell summary without exits only"
    let tS ← Term.exprToSyntax t
    let aS ← Term.exprToSyntax a
    let c0S ← Term.exprToSyntax c0
    let m0S ← Term.exprToSyntax m0
    let HS ← Term.exprToSyntax H
    evalTactic (← `(tactic|
      have $hsum := StrictTS.evalLoop_count_sized $I $P $condS $bodyS $stepS (t := $tS) $encS $wS $aS $m0S $nS ?hn
        $CS $GS $HS ?hH $k0S $s0S $c0S rfl $envS $henv ?hk0 $wS ?hw0 ?hcond ?hF ?hC ?hstep))
    return ← finishCounted hsum .cells neFacts nM ((gs.push C).push H) ret brk k0M
  match cell, κ?, H?, kind? with
  | some K, some κ, some _, some kind =>
    if m == 0 && !ret && !brk then
      -- no mutable variable besides the counter: the fold is over the cell's content alone
      let C1 ← mkFreshExprMVar (← mkArrow finT (← mkArrow κ compT))
      let H1 ← mkFreshExprMVar (← mkArrow finT (← mkArrow κ κ))
      let C1S ← Term.exprToSyntax C1
      let H1S ← Term.exprToSyntax H1
      let KS ← Term.exprToSyntax K
      let κS ← Term.exprToSyntax κ
      let kindS ← Term.exprToSyntax kind
      evalTactic (← `(tactic|
        have $hsum := StrictTS.evalLoop_count_cell1 $I $P $condS $bodyS $stepS (κ := $κS) $encS
          (fun c => { $wS with heap := Std.ExtDHashMap.insert (World.heap $wS) $KS c }) $nS ?hn $C1S $H1S
          $k0S ((Std.ExtDHashMap.get? (World.heap $wS) $KS).getD (HKind.dflt $kindS)) $envS $henv ?hk0
          $wS ?hw0 ?hcond ?hF ?hC ?hstep))
      return ← finishCounted hsum .cell1 neFacts nM #[C1, H1] ret brk k0M
    let some H := H? | throwError "ts_summarize: internal error (no cell step)"
    let KS ← Term.exprToSyntax K
    let κS ← Term.exprToSyntax κ
    let kindS ← Term.exprToSyntax kind
    let HS ← Term.exprToSyntax H
    let thm := mkIdent (if ret then ``StrictTS.evalLoop_count_cells_ret
      else if brk then ``StrictTS.evalLoop_count_cells_brk else ``StrictTS.evalLoop_count_cells)
    evalTactic (← `(tactic|
      have $hsum := $thm $I $P $condS $bodyS $stepS (κ := $κS) $encS
        (fun c => { $wS with heap := Std.ExtDHashMap.insert (World.heap $wS) $KS c }) $nS ?hn $CS $GS $HS
        $k0S $s0S ((Std.ExtDHashMap.get? (World.heap $wS) $KS).getD (HKind.dflt $kindS)) $envS $henv ?hk0
        $wS ?hw0 ?hcond ?hF ?hC ?hstep))
    finishCounted hsum .cells neFacts nM ((gs.push C).push H) ret brk k0M
  | _, _, _, _ =>
    let thm := mkIdent (if ret then ``StrictTS.evalLoop_count_pure_ret
      else if brk then ``StrictTS.evalLoop_count_pure_brk else ``StrictTS.evalLoop_count_pure)
    evalTactic (← `(tactic|
      have $hsum := $thm $I $P $condS $bodyS $stepS $encS $nS ?hn $CS $GS
        $k0S $s0S $envS $henv ?hk0 $wS ?hcond ?hF ?hC ?hstep))
    finishCounted hsum .pure neFacts nM (gs.push C) ret brk k0M
where
  /-- Solve the obligations of a counted-loop summary in order: the condition (which assigns
  `n`), the step, the body (which assigns the step functions), then the side goals. -/
  finishCounted (hsum : Ident) (shape : CountShape) (neFacts : Array (TSyntax `Lean.Parser.Tactic.simpLemma))
      (nM : Lean.Expr) (stepMVars : Array Lean.Expr) (ret : Bool) (brk : Bool) (_k0M : Lean.Expr) :
      TacticM Attempt := do
    let gls ← getGoals
    let hyps := (← heapHyps) ++ neFacts
    let some hcond ← goalTagged gls `hcond | throwError "ts_summarize: internal error (no hcond goal)"
    setGoals [hcond]
    readCountedBound (match shape with | .cells => 3 | _ => 2) nM hyps
    unless ← nM.mvarId!.isAssigned do throwError "ts_summarize: could not read off the loop's bound"
    let some hstep ← goalTagged gls `hstep | throwError "ts_summarize: internal error (no hstep goal)"
    setGoals [hstep]
    match shape with
    | .pure => evalTactic (← `(tactic| intro i s h1))
    | .cells => evalTactic (← `(tactic| intro i s c h1))
    | .cell1 => evalTactic (← `(tactic| intro i c h1))
    evalTactic (← `(tactic| ts_merge [F64.lit_eq_ofNat, ofNat_add_one h1]))
    unless (← getGoals).isEmpty do
      throwError "ts_summarize: the loop's step is not `i = i + 1`; remaining goal:\n{← ppGoal (← getMainGoal)}"
    let some hF ← goalTagged gls `hF | throwError "ts_summarize: internal error (no hF goal)"
    setGoals [hF]
    let iN := mkIdent (← MonadQuotation.addMacroScope `i)
    let sN := mkIdent (← MonadQuotation.addMacroScope `s)
    let cN := mkIdent (← MonadQuotation.addMacroScope `c)
    let names := match shape with
      | .pure => #[iN, sN]
      | .cells => #[iN, sN, cN]
      | .cell1 => #[iN, cN]
    evalTactic (← `(tactic| intro $names*))
    let locals ← withMainContext do
      let lctx ← getLCtx
      return (lctx.getFVarIds.toList.reverse.take names.size).toArray
    -- reading an array at the counter: the counter is a valid index (`i < n`), and an array
    -- index when `omega` proves `i < 2^32 - 1` from the hypotheses
    let iI := iN
    let mut extra := hyps.push (← `(Lean.Parser.Tactic.simpLemma| Fin.isLt $iI:ident))
    -- facts about the position that `omega` proves from `i < n` (checked silently first: a failing
    -- `by omega` inside a term would be logged as an error); they enter as proof terms, not local
    -- hypotheses, since the step function read off below may contain them (in `xs[i]`) and its
    -- metavariable does not see later hypotheses
    let provable (p : Term) : TacticM Bool := withMainContext do
      try
        let pe ← Tactic.elabTerm p (some (mkSort .zero))
        return (← proveProp? (← instantiateMVars pe)
          (← `(tactic| (have := Fin.isLt $iI:ident; omega)))).isSome
      catch _ => return false
    if ← provable (← `((↑$iI : Nat) < 2 ^ 32 - 1)) then
      extra := extra.push (← `(Lean.Parser.Tactic.simpLemma|
        Conv.arrayIndex?_ofNat (n := ↑$iI) (by have := Fin.isLt $iI:ident; omega)))
    -- a position of a string (`s.charAt(i)`, `s[i]`: the bound by `omega` in the merge's second pass)
    if ← provable (← `((↑$iI : Nat) ≤ 2 ^ 53)) then
      extra := extra.push (← `(Lean.Parser.Tactic.simpLemma|
        Conv.toIntegerOrInf_ofNat (n := ↑$iI) (by have := Fin.isLt $iI:ident; omega)))
      extra := extra.push (← `(Lean.Parser.Tactic.simpLemma| JSStr.at?_natCast_of_lt))
    -- the next position `i + 1` (`xs[i + 1]` under the bound `i < xs.length - 1`)
    if ← provable (← `((↑$iI : Nat) + 1 < 2 ^ 32 - 1)) then
      extra := extra.push (← `(Lean.Parser.Tactic.simpLemma|
        ofNat_add_one (n := ↑$iI) (by have := Fin.isLt $iI:ident; omega)))
      extra := extra.push (← `(Lean.Parser.Tactic.simpLemma|
        ofNat_add_lit_one (n := ↑$iI) (by have := Fin.isLt $iI:ident; omega)))
      extra := extra.push (← `(Lean.Parser.Tactic.simpLemma|
        Conv.arrayIndex?_ofNat (n := ↑$iI + 1) (by have := Fin.isLt $iI:ident; omega)))
    let nVal ← instantiateMVars nM
    if nVal.isAppOfArity ``HSub.hSub 6 then
      let aS ← withMainContext <| Term.exprToSyntax (nVal.getArg! 4)
      let cS ← withMainContext <| Term.exprToSyntax (nVal.getArg! 5)
      if ← provable (← `((↑$iI : Nat) + $cS < $aS)) then
        extra := extra.push (← `(Lean.Parser.Tactic.simpLemma|
          (show (↑$iI : Nat) + $cS < $aS by have := Fin.isLt $iI:ident; omega)))
        extra := extra.push (← `(Lean.Parser.Tactic.simpLemma|
          (show (↑$iI : Nat) < $aS by have := Fin.isLt $iI:ident; omega)))
    evalTactic (← `(tactic| ts_merge [$extra,*]))
    unless (← getGoals).isEmpty do
      return .stuck (← getMainGoal) locals
    for g in stepMVars do
      unless ← g.mvarId!.isAssigned do
        throwError "ts_summarize: could not read off the step function"
    let some hC ← goalTagged gls `hC | throwError "ts_summarize: internal error (no hC goal)"
    setGoals [hC]
    try
      if ret then evalTactic (← `(tactic| (intro $names*; simp [Completion.isNextOrRet_ite, iteStaleInstance])))
      else if brk then evalTactic (← `(tactic| (intro $names*; simp [Completion.isNextOrBrk_ite, iteStaleInstance])))
      else evalTactic (← `(tactic| (intro $names*; simp [Completion.isNext_ite, iteStaleInstance])))
    catch _ => return .notNext
    unless (← getGoals).isEmpty do return .notNext
    let rest := gls.filter (fun g => g != hcond && g != hstep && g != hF && g != hC)
    let main := rest.head!
    -- side goals: `n ≤ 2^53`, `k0 ≤ n`, the cell's world
    let mut side := #[]
    for g in rest.tail! do
      let tag := (← g.getTag).eraseMacroScopes
      setGoals [g]
      if tag == `hn || tag == `hk0 then
        try evalTactic (← `(tactic| first | omega | (simp; done) | decide)) catch _ => pure ()
        side := side ++ (← getGoals).toArray
      else if tag == `hH then
        -- a fixed-size cell: the iteration keeps the array's size (`xs[j] = v`, swaps)
        try evalTactic (← `(tactic| (intro i s c; first
          | (simp [StrictTS.sized_size]; done)
          | ((repeat' split) <;> simp [StrictTS.sized_size]))))
        catch _ => pure ()
        unless (← getGoals).isEmpty do
          throwError "ts_summarize: the iteration may change the size of the array it writes"
      else
        closeSideGoals [g]
        side := side ++ (← getGoals).toArray
    setGoals [main]
    evalTactic (← `(tactic| rw [$hsum:ident]))
    -- (the rewrite may close the goal: both sides summarized to the same fold)
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| clear $hsum:ident))
    -- with `return`, the code after the loop runs for both completions (the step function uses
    -- the position in the returned value, so it stays a fold over the positions)
    unless (← getGoals).isEmpty do
      if ret then splitRet neFacts else if !brk then elemFold
    unless (← getGoals).isEmpty do clearNeFacts
    setGoals ((← getGoals) ++ side.toList)
    return .done
  /-- When the loop runs over all positions of an array `xs` (`n = xs.size`, from 0) and its
  step function uses the position only to read `xs[i]`, rewrite the fold over positions to the
  fold over the elements, `xs.toList.foldl F s0` (the form of a `for … of` summary). -/
  elemFold : TacticM Unit := withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    let some fo := goal.find? (fun e => e.isAppOfArity ``List.foldl 5 &&
        (e.getArg! 4).isAppOfArity ``List.drop 3 && ((e.getArg! 4).getArg! 2).isAppOf ``List.finRange)
      | return
    let f := fo.getArg! 2
    let s0 := fo.getArg! 3
    let dr := fo.getArg! 4
    let k0 ← whnfR (dr.getArg! 1)
    unless (← isDefEq k0 (mkNatLit 0)) do return
    let n ← instantiateMVars ((dr.getArg! 2).appArg!)
    unless n.isAppOf ``Array.size do return
    let xs := n.appArg!
    let some F ← lambdaTelescope f (fun bs body => do
        unless bs.size == 2 do return none
        let st := bs[0]!
        let i := bs[1]!
        let elT := (← whnfR (← inferType xs)).appArg!
        withLocalDeclD `x elT fun x => do
          let body' := body.replace fun e =>
            if e.isAppOfArity ``GetElem.getElem 8 && e.getArg! 5 == xs &&
                (e.getArg! 6).isAppOfArity ``Fin.val 2 && (e.getArg! 6).appArg! == i then some x else none
          if body'.containsFVar i.fvarId! then return none
          return some (← mkLambdaFVars #[st, x] body'))
      | return
    let xsS ← Term.exprToSyntax xs
    let FS ← Term.exprToSyntax F
    let s0S ← Term.exprToSyntax s0
    let foS ← Term.exprToSyntax fo
    -- (without error recovery: a failing inner `rw` must undo the rewrite, not be logged)
    let saved ← saveState
    try withoutRecover do
      evalTactic (← `(tactic| rw [show $foS = List.foldl $FS $s0S (Array.toList $xsS) by
        rw [List.drop_zero]; exact foldl_finRange_getElem $xsS $FS $s0S]))
    catch _ => saved.restore

/-- The step `i = i - 1` of a backwards counted loop. -/
def Summarize.isDecStep (step : Lean.Expr) : MetaM Bool := do
  let st ← whnfR step
  unless st.isAppOfArity ``Block.seq 5 do return false
  let s ← whnfR (st.getArg! 3)
  unless s.isAppOfArity ``Stmt.assign 6 do return false
  return ((s.getArg! 5).find? (·.isConstOf ``NumBin.sub)).isSome

/-- The natural number denoted by a double that is a literal or `F64.ofNat n`. -/
def Summarize.natOfF64? (e : Lean.Expr) : Option Lean.Expr :=
  let fix (e : Lean.Expr) : Lean.Expr := match e with
    | .lit (.natVal v) => mkNatLit v
    | e => e
  if e.isAppOfArity ``F64.ofNat 1 then some (fix e.appArg!)
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.getArg! 1 with
    | .lit (.natVal v) => some (mkNatLit v)
    | _ => none
  else none

/-- The counter of a backwards `while` loop: the slot that the last statement of the body
decrements (`i = i - 1`). -/
partial def Summarize.lastDecSlot (body : Lean.Expr) : MetaM (Option Nat) := do
  let b ← whnfR body
  unless b.isAppOfArity ``Block.seq 5 do return none
  let rest ← whnfR (b.getArg! 4)
  if rest.isAppOf ``Block.nil then
    let st ← whnfR (b.getArg! 3)
    unless st.isAppOfArity ``Stmt.assign 6 do return none
    unless ((st.getArg! 5).find? (·.isConstOf ``NumBin.sub)).isSome do return none
    Summarize.varPos (st.getArg! 4)
  else Summarize.lastDecSlot rest

/-- One summarization attempt for a backwards counted loop `for (let i = x0; P(i); i--)` with
`x0 = xs.length - 1` or a literal: world unchanged (`cell = none`) or cell `K` written; `ret`/`brk`
for `return`/`break` in the body. -/
def summarizeDownAttempt (cell : Option Lean.Expr)
    (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) (ret : Bool := false) (brk : Bool := false)
    (retw : Bool := false) (whileMode : Bool := false) :
    TacticM Attempt := do
  let ret := ret || retw
  let neFacts := (← heapNeFacts) ++ extra
  withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop)
    | throwError "ts_summarize: no loop (evalForOf/evalLoop) in the goal"
  let loop := e.getArg! 2
  let w0 := e.getArg! 3
  let args := loop.getAppArgs
  let TT := args[0]!
  let Γ := args[3]!
  let ρ := args[4]!
  let env0 := args[8]!
  let some j ← (if whileMode then Summarize.lastDecSlot args[6]! else Summarize.counterSlot args[7]!)
    | throwError "ts_summarize: the loop's step is not an assignment of a counter (`i = i - 1`)"
  let spine ← Summarize.ctxSpine Γ
  let mut isMut : Array Bool := #[]
  let mut tys : Array Lean.Expr := #[]
  for (sl, _) in spine do
    let m ← whnf (mkApp (mkConst ``Slot.mutable) sl)
    isMut := isMut.push (m.isConstOf ``Bool.true)
    tys := tys.push (← whnf (mkApp (mkConst ``Slot.ty) sl))
  unless j < spine.size && isMut[j]! && tys[j]!.isConstOf ``Ty.num do
    throwError "ts_summarize: the loop's counter is not a mutable `number` variable"
  let comps ← Summarize.envComps env0 spine.size
  let mutIdx := (List.range spine.size).filter (fun i => isMut[i]!)
  -- (mutable variables that the loop never assigns keep their values: not part of the state)
  let assigned? ← Summarize.assignedSlots #[(args[6]!, 0), (args[7]!, 0)]
  let others := mutIdx.filter (fun i => i != j && assigned?.all (·.contains i))
  let valTys := others.map (fun i => mkApp2 (mkConst ``Val) TT tys[i]!)
  let σ ← Summarize.mkProdTy valTys
  let m := others.length
  let natT := mkConst ``Nat
  let enc ← withLocalDeclD `x (mkConst ``F64) fun x => withLocalDeclD `s σ fun s => do
    let ps ← Summarize.tupleProjs s m
    let cnt := mkApp2 (mkConst ``Val.num) TT x
    let mut muts : Array Lean.Expr := #[]
    let mut q := 0
    for i in mutIdx do
      if i == j then muts := muts.push cnt
      else if others.contains i then
        muts := muts.push ps[q]!
        q := q + 1
      else muts := muts.push comps[i]!
    mkLambdaFVars #[x, s] (← Summarize.mkEnvLit TT spine isMut comps muts.toList)
  let s0 ← Summarize.mkTuple (others.map (fun i => comps[i]!))
  -- the start `x0 = N - 1`: `a - 1` (a length minus one) or a literal `k0 = (k0 + 1) - 1`
  let cv ← whnfR comps[j]!
  let x0 := if cv.isAppOf ``Val.num then cv.appArg! else cv
  let N ← if x0.isAppOfArity ``HSub.hSub 6 &&
        (Summarize.natOfF64? (x0.getArg! 5)) == some (mkNatLit 1) then
      match Summarize.natOfF64? (x0.getArg! 4) with
      | some a => pure a
      | none => throwError "ts_summarize: the start of the backwards loop is not `n - 1` or a literal"
    else match Summarize.natOfF64? x0 with
      | some k0 => mkAppM ``HAdd.hAdd #[k0, mkNatLit 1]
      | none => throwError "ts_summarize: the start of the backwards loop is not `n - 1` or a literal"
  let mM ← mkFreshExprMVar natT
  let PcM ← mkFreshExprMVar (← mkArrow natT (mkConst ``Bool))
  let finT := mkApp (mkConst ``Fin) N
  let compT := mkApp2 (mkConst ``Completion) TT ρ
  let kind? ← cell.mapM fun K => do
    if K.isAppOfArity ``Prod.mk 4 then pure (K.getArg! 2) else mkAppM ``Prod.fst #[K]
  let κ ← match ← kind?.mapM (fun kind => whnfR (mkApp2 (mkConst ``HKind.Cell) TT kind)) with
    | some κ => pure κ
    | none => pure (mkConst ``Unit)
  let arrows (res : Lean.Expr) : MetaM Lean.Expr := do mkArrow finT (← mkArrow σ (← mkArrow κ res))
  let mut gs : Array Lean.Expr := #[]
  for vt in valTys do
    gs := gs.push (← mkFreshExprMVar (← arrows vt))
  let C ← mkFreshExprMVar (← arrows compT)
  let H? ← if cell.isSome then some <$> mkFreshExprMVar (← arrows κ) else pure none
  let G ← withLocalDeclD `i finT fun i => withLocalDeclD `s σ fun s => withLocalDeclD `c κ fun c => do
    mkLambdaFVars #[i, s, c] (← Summarize.mkTuple (gs.toList.map (fun g => mkApp3 g i s c)))
  let I ← Term.exprToSyntax args[1]!
  let P ← Term.exprToSyntax args[2]!
  let condS ← Term.exprToSyntax args[5]!
  let bodyS ← Term.exprToSyntax args[6]!
  let stepS ← Term.exprToSyntax args[7]!
  let encS ← Term.exprToSyntax enc
  let GS ← Term.exprToSyntax G
  let CS ← Term.exprToSyntax C
  let NS ← Term.exprToSyntax N
  let mS ← Term.exprToSyntax mM
  let PcS ← Term.exprToSyntax PcM
  let x0S ← Term.exprToSyntax x0
  let s0S ← Term.exprToSyntax s0
  let envS ← Term.exprToSyntax env0
  let wS ← Term.exprToSyntax w0
  let κS ← Term.exprToSyntax κ
  let hsum := mkIdent `hsum
  let henv ← `(by first | rfl | simp only [Env.cons_head_tail])
  let (putS, c0S, HS) ← match cell, H?, kind? with
    | some K, some H, some kind => do
      let KS ← Term.exprToSyntax K
      let kindS ← Term.exprToSyntax kind
      pure (← `(fun c => { $wS with heap := Std.ExtDHashMap.insert (World.heap $wS) $KS c }),
        ← `((Std.ExtDHashMap.get? (World.heap $wS) $KS).getD (HKind.dflt $kindS)), ← Term.exprToSyntax H)
    | _, _, _ => pure (← `(fun (_ : Unit) => $wS), ← `(()), ← `(fun _ _ _ => ()))
  -- with `retw`, the world after an iteration is read off too (`?W`)
  let WM ← mkFreshExprMVar (← arrows (mkConst ``World [] |>.app TT))
  if whileMode then
    evalTactic (← `(tactic|
      have $hsum := StrictTS.evalLoop_down_while_cells $I $P $condS $bodyS (κ := $κS) $encS $putS $NS $mS
        ?hN ?hmN $PcS $CS $GS $HS $x0S ?hx0 $s0S $c0S $envS $henv $wS ?hw0 ?hcond ?hP ?hPm ?hF ?hC))
  else if retw then
    let WS ← Term.exprToSyntax WM
    evalTactic (← `(tactic|
      have $hsum := StrictTS.evalLoop_down_cells_retw $I $P $condS $bodyS $stepS (κ := $κS) $encS $putS $NS $mS
        ?hN ?hmN $PcS $CS $GS $HS $WS $x0S ?hx0 $s0S $c0S $envS $henv $wS ?hw0 ?hcond ?hP ?hPm ?hF ?hW ?hC ?hstep))
  else
    let thm := mkIdent (if ret then ``StrictTS.evalLoop_down_cells_ret
      else if brk then ``StrictTS.evalLoop_down_cells_brk else ``StrictTS.evalLoop_down_cells)
    evalTactic (← `(tactic|
      have $hsum := $thm $I $P $condS $bodyS $stepS (κ := $κS) $encS $putS $NS $mS ?hN ?hmN $PcS $CS $GS $HS
        $x0S ?hx0 $s0S $c0S $envS $henv $wS ?hw0 ?hcond ?hP ?hPm ?hF ?hC ?hstep))
  let gls ← getGoals
  let hyps := (← heapHyps) ++ neFacts
  -- the condition at time `k` (counter `k - 1`): read off, then the stop time `m`
  let some hcond ← goalTagged gls `hcond | throwError "ts_summarize: internal error (no hcond goal)"
  setGoals [hcond]
  evalTactic (← `(tactic| intro k s c hk))
  evalTactic (← `(tactic| ts_merge [F64.lit_eq_ofNat, $hyps,*]))
  unless (← getGoals).isEmpty && (← PcM.mvarId!.isAssigned) do
    throwError "ts_summarize: the condition of the backwards loop does not evaluate on a symbolic state"
  let mVal ← do
    let pc ← instantiateMVars PcM
    let some b := (pc.find? fun e => e.isAppOfArity ``F64.le 2 || e.isAppOfArity ``F64.lt 2 ||
        e.isAppOfArity ``F64.ge 2 || e.isAppOfArity ``F64.gt 2)
      | throwError "ts_summarize: the condition of the backwards loop is not `i >= c` or `i > c`"
    let (lower, strict) :=
      if b.isAppOfArity ``F64.ge 2 then (b.getArg! 1, false)
      else if b.isAppOfArity ``F64.gt 2 then (b.getArg! 1, true)
      else if b.isAppOfArity ``F64.le 2 then (b.getArg! 0, false)
      else (b.getArg! 0, true)
    let some c' := Summarize.natOfF64? lower
      | throwError "ts_summarize: the condition of the backwards loop is not `i >= c` or `i > c` with `c` a literal"
    if c'.hasLooseBVars then
      throwError "ts_summarize: the condition of the backwards loop is not `i >= c` or `i > c`"
    let m' ← if strict then mkAppM ``HAdd.hAdd #[c', mkNatLit 1] else pure c'
    mkAppM ``Min.min #[m', N]
  unless ← isDefEq mM mVal do throwError "ts_summarize: could not read off the loop's stop"
  let condLemmas ← `(tactic|
    simp (disch := omega) only [StrictTS.F64.ge, StrictTS.F64.gt, le_ofNat_sub_ofNat_eq,
      lt_ofNat_sub_ofNat_eq, lt_ofNat, le_ofNat, decide_eq_true_eq, decide_eq_false_iff_not, Nat.add_sub_cancel])
  for tag in [`hP, `hPm] do
    let some g ← goalTagged gls tag | throwError "ts_summarize: internal error (no {tag} goal)"
    setGoals [g]
    try
      if tag == `hP then evalTactic (← `(tactic| intro k h1 h2))
      -- the read-off condition, instantiated and beta-reduced
      let g ← getMainGoal
      replaceMainGoal [← g.replaceTargetDefEq (← instantiateMVars (← g.getType)).headBeta]
      evalTactic condLemmas
      unless (← getGoals).isEmpty do evalTactic (← `(tactic| omega))
    catch _ => pure ()
    unless (← getGoals).isEmpty do
      throwError "ts_summarize: the condition of the backwards loop does not hold down to its stop; \
        remaining goal:\n{← ppGoal (← getMainGoal)}"
  -- the step `i = i - 1` (in a `while` loop, the end of the body)
  let hstepName ← if whileMode then pure none else do
    let some hstep ← goalTagged gls `hstep | throwError "ts_summarize: internal error (no hstep goal)"
    setGoals [hstep]
    evalTactic (← `(tactic| intro i s c))
    evalTactic (← `(tactic| ts_merge [F64.lit_eq_ofNat, $hyps,*]))
    unless (← getGoals).isEmpty do
      throwError "ts_summarize: the loop's step is not `i = i - 1`; remaining goal:\n{← ppGoal (← getMainGoal)}"
    pure (some hstep.name)
  -- the body at a position
  let some hF ← goalTagged gls `hF | throwError "ts_summarize: internal error (no hF goal)"
  setGoals [hF]
  let iN := mkIdent (← MonadQuotation.addMacroScope `i)
  let sN := mkIdent (← MonadQuotation.addMacroScope `s)
  let cN := mkIdent (← MonadQuotation.addMacroScope `c)
  evalTactic (← `(tactic| intro $iN:ident $sN:ident $cN:ident))
  let locals ← withMainContext do
    let lctx ← getLCtx
    return (lctx.getFVarIds.toList.reverse.take 3).toArray
  let mut extraF := hyps.push (← `(Lean.Parser.Tactic.simpLemma| Fin.isLt $iN:ident))
  let ok ← withMainContext do
    try
      let pe ← Tactic.elabTerm (← `((↑$iN : Nat) < 2 ^ 32 - 1)) (some (mkSort .zero))
      return (← proveProp? (← instantiateMVars pe) (← `(tactic| (have := Fin.isLt $iN:ident; omega)))).isSome
    catch _ => return false
  if ok then
    extraF := extraF.push (← `(Lean.Parser.Tactic.simpLemma|
      Conv.arrayIndex?_ofNat (n := ↑$iN) (by have := Fin.isLt $iN:ident; omega)))
  -- the counter step at the end of a `while` body: `i - 1` stays `ofNat i - ofNat 1`
  if whileMode then
    extraF := extraF.push (← `(Lean.Parser.Tactic.simpLemma| F64.lit_eq_ofNat))
  -- string concatenations of the step right-associated (`out + String(i) + " "` and
  -- `` out += `${i} ` `` give the same step)
  extraF := extraF.push (← `(Lean.Parser.Tactic.simpLemma| JSStr.append_assoc))
  evalTactic (← `(tactic| ts_merge [$extraF,*]))
  unless (← getGoals).isEmpty do
    return .stuck (← getMainGoal) locals
  for g in gs.push C do
    unless ← g.mvarId!.isAssigned do throwError "ts_summarize: could not read off the step function"
  -- with `retw`: an iteration that goes on leaves the world as `put (H …)`
  if retw then
    let some hW ← goalTagged gls `hW | throwError "ts_summarize: internal error (no hW goal)"
    setGoals [hW]
    try evalTactic (← `(tactic| (intro i s c h; revert h; first | (simp; done) | (split <;> simp_all))))
    catch _ => return .notNext
    unless (← getGoals).isEmpty do return .notNext
  let some hC ← goalTagged gls `hC | throwError "ts_summarize: internal error (no hC goal)"
  setGoals [hC]
  try
    if ret then evalTactic (← `(tactic| (intro i s c; simp [Completion.isNextOrRet_ite, iteStaleInstance])))
    else if brk then evalTactic (← `(tactic| (intro i s c; simp [Completion.isNextOrBrk_ite, iteStaleInstance])))
    else evalTactic (← `(tactic| (intro i s c; simp [Completion.isNext_ite, iteStaleInstance])))
  catch _ => return .notNext
  unless (← getGoals).isEmpty do return .notNext
  -- side goals: `N ≤ 2^53`, `m ≤ N`, the start, the cell's world
  let rest ← gls.filterM (fun g => do
    let tag := (← g.getTag).eraseMacroScopes
    return g.name != hcond.name && some g.name != hstepName && g.name != hF.name && g.name != hC.name && tag != `hW)
  let main := rest.head!
  let mut side := #[]
  for g in rest.tail! do
    let tag := (← g.getTag).eraseMacroScopes
    if tag == `hP || tag == `hPm then continue
    setGoals [g]
    if tag == `hN || tag == `hmN then
      try evalTactic (← `(tactic| first | omega | (simp; done) | decide)) catch _ => pure ()
    else if tag == `hx0 then
      try evalTactic (← `(tactic| first | rfl | (rw [ofNat_sub_ofNat (by omega) (by omega), Nat.add_sub_cancel])))
      catch _ => pure ()
    else
      closeSideGoals [g]
    side := side ++ (← getGoals).toArray
  setGoals [main]
  evalTactic (← `(tactic| rw [$hsum:ident]))
  -- (the rewrite may close the goal: both sides summarized to the same fold)
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| clear $hsum:ident))
  if ret && !(← getGoals).isEmpty then splitRet neFacts
  unless (← getGoals).isEmpty do clearNeFacts
  setGoals ((← getGoals) ++ side.toList)
  return .done

/-- The counter of a counted `while` loop: the slot that the last statement of the body increments
(`i = i + 1`). -/
partial def Summarize.lastIncSlot (body : Lean.Expr) : MetaM (Option Nat) := do
  let b ← whnfR body
  unless b.isAppOfArity ``Block.seq 5 do return none
  let rest ← whnfR (b.getArg! 4)
  if rest.isAppOf ``Block.nil then
    let st ← whnfR (b.getArg! 3)
    unless st.isAppOfArity ``Stmt.assign 6 do return none
    unless ((st.getArg! 5).find? (·.isConstOf ``NumBin.add)).isSome do return none
    Summarize.varPos (st.getArg! 4)
  else Summarize.lastIncSlot rest

/-- One summarization attempt for a counted `while (i < n) { …; i++ }` loop (no `break`/`return`):
world unchanged (`cell = none`) or cell `K` written. -/
def summarizeWhileUpAttempt (cell : Option Lean.Expr)
    (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) : TacticM Attempt := do
  let neFacts := (← heapNeFacts) ++ extra
  withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop)
    | throwError "ts_summarize: no loop in the goal"
  let loop := e.getArg! 2
  let w0 := e.getArg! 3
  let args := loop.getAppArgs
  let TT := args[0]!
  let Γ := args[3]!
  let ρ := args[4]!
  let env0 := args[8]!
  let some j ← Summarize.lastIncSlot args[6]!
    | throwError "ts_summarize: the while loop's body does not end with a counter step (`i++`)"
  let spine ← Summarize.ctxSpine Γ
  let mut isMut : Array Bool := #[]
  let mut tys : Array Lean.Expr := #[]
  for (sl, _) in spine do
    let m ← whnf (mkApp (mkConst ``Slot.mutable) sl)
    isMut := isMut.push (m.isConstOf ``Bool.true)
    tys := tys.push (← whnf (mkApp (mkConst ``Slot.ty) sl))
  unless j < spine.size && isMut[j]! && tys[j]!.isConstOf ``Ty.num do
    throwError "ts_summarize: the while loop's counter is not a mutable `number` variable"
  let comps ← Summarize.envComps env0 spine.size
  let mutIdx := (List.range spine.size).filter (fun i => isMut[i]!)
  -- (mutable variables that the loop never assigns keep their values: not part of the state)
  let assigned? ← Summarize.assignedSlots #[(args[6]!, 0), (args[7]!, 0)]
  let others := mutIdx.filter (fun i => i != j && assigned?.all (·.contains i))
  let valTys := others.map (fun i => mkApp2 (mkConst ``Val) TT tys[i]!)
  let σ ← Summarize.mkProdTy valTys
  let m := others.length
  let natT := mkConst ``Nat
  let enc ← withLocalDeclD `k natT fun k => withLocalDeclD `s σ fun s => do
    let ps ← Summarize.tupleProjs s m
    let cnt := mkApp2 (mkConst ``Val.num) TT (← mkAppM ``F64.ofNat #[k])
    let mut muts : Array Lean.Expr := #[]
    let mut q := 0
    for i in mutIdx do
      if i == j then muts := muts.push cnt
      else if others.contains i then
        muts := muts.push ps[q]!
        q := q + 1
      else muts := muts.push comps[i]!
    mkLambdaFVars #[k, s] (← Summarize.mkEnvLit TT spine isMut comps muts.toList)
  let s0 ← Summarize.mkTuple (others.map (fun i => comps[i]!))
  let nM ← mkFreshExprMVar natT
  let cv ← whnfR comps[j]!
  let x0 := if cv.isAppOf ``Val.num then cv.appArg! else cv
  let some k0 := Summarize.natOfF64? x0
    | throwError "ts_summarize: the while loop's counter does not start at a literal"
  let finT := mkApp (mkConst ``Fin) nM
  let compT := mkApp2 (mkConst ``Completion) TT ρ
  let kind? ← cell.mapM fun K => do
    if K.isAppOfArity ``Prod.mk 4 then pure (K.getArg! 2) else mkAppM ``Prod.fst #[K]
  let κ ← match ← kind?.mapM (fun kind => whnfR (mkApp2 (mkConst ``HKind.Cell) TT kind)) with
    | some κ => pure κ
    | none => pure (mkConst ``Unit)
  let arrows (res : Lean.Expr) : MetaM Lean.Expr := do mkArrow finT (← mkArrow σ (← mkArrow κ res))
  let mut gs : Array Lean.Expr := #[]
  for vt in valTys do
    gs := gs.push (← mkFreshExprMVar (← arrows vt))
  let C ← mkFreshExprMVar (← arrows compT)
  let H? ← if cell.isSome then some <$> mkFreshExprMVar (← arrows κ) else pure none
  let G ← withLocalDeclD `i finT fun i => withLocalDeclD `s σ fun s => withLocalDeclD `c κ fun c => do
    mkLambdaFVars #[i, s, c] (← Summarize.mkTuple (gs.toList.map (fun g => mkApp3 g i s c)))
  let I ← Term.exprToSyntax args[1]!
  let P ← Term.exprToSyntax args[2]!
  let condS ← Term.exprToSyntax args[5]!
  let bodyS ← Term.exprToSyntax args[6]!
  let encS ← Term.exprToSyntax enc
  let GS ← Term.exprToSyntax G
  let CS ← Term.exprToSyntax C
  let nS ← Term.exprToSyntax nM
  let k0S ← Term.exprToSyntax k0
  let s0S ← Term.exprToSyntax s0
  let envS ← Term.exprToSyntax env0
  let wS ← Term.exprToSyntax w0
  let κS ← Term.exprToSyntax κ
  let hsum := mkIdent `hsum
  let henv ← `(by first | rfl | simp only [Env.cons_head_tail])
  let (putS, c0S, HS) ← match cell, H?, kind? with
    | some K, some H, some kind => do
      let KS ← Term.exprToSyntax K
      let kindS ← Term.exprToSyntax kind
      pure (← `(fun c => { $wS with heap := Std.ExtDHashMap.insert (World.heap $wS) $KS c }),
        ← `((Std.ExtDHashMap.get? (World.heap $wS) $KS).getD (HKind.dflt $kindS)), ← Term.exprToSyntax H)
    | _, _, _ => pure (← `(fun (_ : Unit) => $wS), ← `(()), ← `(fun _ _ _ => ()))
  evalTactic (← `(tactic|
    have $hsum := StrictTS.evalLoop_while_up_cells $I $P $condS $bodyS (κ := $κS) $encS $putS $nS ?hn $CS $GS $HS
      $k0S $s0S $c0S $envS $henv ?hk0 $wS ?hw0 ?hcond ?hF ?hC))
  let gls ← getGoals
  let hyps := (← heapHyps) ++ neFacts
  let some hcond ← goalTagged gls `hcond | throwError "ts_summarize: internal error (no hcond goal)"
  setGoals [hcond]
  readCountedBound 3 nM hyps
  unless ← nM.mvarId!.isAssigned do throwError "ts_summarize: could not read off the loop's bound"
  let some hF ← goalTagged gls `hF | throwError "ts_summarize: internal error (no hF goal)"
  setGoals [hF]
  let iN := mkIdent (← MonadQuotation.addMacroScope `i)
  let sN := mkIdent (← MonadQuotation.addMacroScope `s)
  let cN := mkIdent (← MonadQuotation.addMacroScope `c)
  evalTactic (← `(tactic| intro $iN:ident $sN:ident $cN:ident))
  let locals ← withMainContext do
    let lctx ← getLCtx
    return (lctx.getFVarIds.toList.reverse.take 3).toArray
  let mut extraF := hyps.push (← `(Lean.Parser.Tactic.simpLemma| Fin.isLt $iN:ident))
  let provable (p : Term) : TacticM Bool := withMainContext do
    try
      let pe ← Tactic.elabTerm p (some (mkSort .zero))
      return (← proveProp? (← instantiateMVars pe)
        (← `(tactic| (have := Fin.isLt $iN:ident; omega)))).isSome
    catch _ => return false
  if ← provable (← `((↑$iN : Nat) < 2 ^ 32 - 1)) then
    extraF := extraF.push (← `(Lean.Parser.Tactic.simpLemma|
      Conv.arrayIndex?_ofNat (n := ↑$iN) (by have := Fin.isLt $iN:ident; omega)))
  -- the counter step at the end of the body
  if ← provable (← `((↑$iN : Nat) + 1 ≤ 2 ^ 53)) then
    extraF := extraF.push (← `(Lean.Parser.Tactic.simpLemma|
      ofNat_add_one (n := ↑$iN) (by have := Fin.isLt $iN:ident; omega)))
    extraF := extraF.push (← `(Lean.Parser.Tactic.simpLemma|
      ofNat_add_lit_one (n := ↑$iN) (by have := Fin.isLt $iN:ident; omega)))
  evalTactic (← `(tactic| ts_merge [$extraF,*]))
  unless (← getGoals).isEmpty do
    return .stuck (← getMainGoal) locals
  for g in gs.push C do
    unless ← g.mvarId!.isAssigned do throwError "ts_summarize: could not read off the step function"
  let some hC ← goalTagged gls `hC | throwError "ts_summarize: internal error (no hC goal)"
  setGoals [hC]
  try evalTactic (← `(tactic| (intro i s c; simp [Completion.isNext_ite, iteStaleInstance])))
  catch _ => return .notNext
  unless (← getGoals).isEmpty do return .notNext
  let rest := gls.filter (fun g => g.name != hcond.name && g.name != hF.name && g.name != hC.name)
  let main := rest.head!
  let mut side := #[]
  for g in rest.tail! do
    let tag := (← g.getTag).eraseMacroScopes
    setGoals [g]
    if tag == `hn || tag == `hk0 then
      try evalTactic (← `(tactic| first | omega | (simp; done) | decide)) catch _ => pure ()
    else
      closeSideGoals [g]
    side := side ++ (← getGoals).toArray
  setGoals [main]
  evalTactic (← `(tactic| rw [$hsum:ident]))
  -- (the rewrite may close the goal: both sides summarized to the same fold)
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| clear $hsum:ident))
  unless (← getGoals).isEmpty do clearNeFacts
  setGoals ((← getGoals) ++ side.toList)
  return .done

/-- The call lemmas (`f_call`, `fDef`, as the translator emits them) of the non-recursive
top-level functions that the expression `e` (a loop body) calls, so that the body's symbolic
execution runs them. -/
def Summarize.calleeLemmas (e : Lean.Expr) : MetaM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let env ← getEnv
  let mut out := #[]
  let mut seen : Array Name := #[]
  for c in (e.getUsedConstants) do
    let str := c.getString!
    unless str.endsWith "Ref" && !seen.contains c do continue
    seen := seen.push c
    let base := String.ofList (str.toList.take (str.length - 3))
    let lem := c.getPrefix.str (base ++ "_call")
    let defn := c.getPrefix.str (base ++ "Def")
    unless env.contains lem && env.contains defn do continue
    -- not recursive: its definition does not mention its own reference
    let some info := env.find? defn | continue
    let some v := info.value? | continue
    if v.getUsedConstants.contains c then continue
    out := out.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent lem):ident))
    out := out.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent defn):ident))
  return out

/-- The start of a backwards counted loop that the summaries read: `a - 1` or a natural literal. -/
def Summarize.downStartKnown (x0 : Lean.Expr) : Bool :=
  (x0.isAppOfArity ``HSub.hSub 6 && Summarize.natOfF64? (x0.getArg! 5) == some (mkNatLit 1) &&
    (Summarize.natOfF64? (x0.getArg! 4)).isSome) || (Summarize.natOfF64? x0).isSome

/-- What `startSplit` did to the first loop of the goal. -/
inductive StartSplit where
  /-- nothing: the loop's start is read as it is, or not handled -/
  | none
  /-- the main goal is the case where the loop runs, its start now `ofNat k` -/
  | runs
  /-- the loop runs no iteration (rewritten away) -/
  | zero

/-- A backwards counted loop (the first loop of the goal) whose counter starts at the computed
value `x0 = Math.min(Math.floor(n), m)` (`m` a literal): split on the loop's condition `i > c`
at the start (`c` a literal), read off as `b`. When it holds, `x0` is `ofNat (min x0.natVal m)`
(`F64.floor_min_eq_ofNat_min`: NaN, `-Infinity` and `-0` are not above `c`, `+Infinity` gives
`m`), and every `x0` in the goal is rewritten so. When it does not, the loop runs no iteration,
nor do the other loops of the goal that the same test stops (the other side of an
equivalence); that case must then close by `simp`, else nothing is changed. A hypothesis that
decides the test takes its case without a split; with `decidedOnly`, only then. -/
partial def startSplit (hyps : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (decidedOnly : Bool := false) :
    TacticM StartSplit := do
  let saved ← saveState
  let fail : TacticM StartSplit := do saved.restore; return .none
  try
    let some (loop, w0, x0, m) ← withMainContext do
        let goal ← instantiateMVars (← getMainTarget)
        let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop)
          | return none
        let loop := e.getArg! 2
        let args := loop.getAppArgs
        let step ← whnfR args[7]!
        let j? ← if step.isAppOf ``Block.nil then Summarize.lastDecSlot args[6]!
          else if ← Summarize.isDecStep args[7]! then Summarize.counterSlot args[7]! else pure none
        let some j := j? | return none
        let spine ← Summarize.ctxSpine args[3]!
        unless j < spine.size do return none
        let comps ← Summarize.envComps args[8]! spine.size
        let cv ← whnfR comps[j]!
        let x0 := if cv.isAppOf ``Val.num then cv.appArg! else cv
        if Summarize.downStartKnown x0 then return none
        unless x0.isAppOfArity ``F64.min 2 && (x0.getArg! 0).isAppOfArity ``F64.floor 1 do return none
        let some m := Summarize.natOfF64? (x0.getArg! 1) | return none
        return some (loop, e.getArg! 3, x0, m)
      | fail
    let args := loop.getAppArgs
    let bM ← withMainContext <| mkFreshExprMVar (mkConst ``Bool)
    let hb := mkIdent (← mkFreshUserName `hstart)
    let hz := mkIdent (← mkFreshUserName `hzero)
    let (I, P, condS, bodyS, stepS, envS, wS, bS, x0S, mS) ← withMainContext do
      return (← Term.exprToSyntax args[1]!, ← Term.exprToSyntax args[2]!, ← Term.exprToSyntax args[5]!,
        ← Term.exprToSyntax args[6]!, ← Term.exprToSyntax args[7]!, ← Term.exprToSyntax args[8]!,
        ← Term.exprToSyntax w0, ← Term.exprToSyntax bM, ← Term.exprToSyntax x0, ← Term.exprToSyntax m)
    let outer ← getMainGoal
    evalTactic (← `(tactic| refine StrictTS.evalLoop_split_start $I $P $condS $bodyS $stepS $envS $wS $bS
      ?_ (fun $hb:ident => ?_) (fun $hb:ident $hz:ident => ?_)))
    let gs ← getGoals
    let some gc := gs[0]? | fail
    let some gp := gs[1]? | fail
    let some gn := gs[2]? | fail
    let rest := gs.drop 3
    -- the condition at the start, read off
    setGoals [gc]
    evalTactic (← `(tactic| ts_merge [F64.lit_eq_ofNat, $hyps,*]))
    unless (← getGoals).isEmpty && (← bM.mvarId!.isAssigned) do return ← fail
    let b ← instantiateMVars bM
    -- `i > c`, i.e. `c < i`
    let lower? := if b.isAppOfArity ``F64.gt 2 then Summarize.natOfF64? (b.getArg! 1)
      else if b.isAppOfArity ``F64.lt 2 then Summarize.natOfF64? (b.getArg! 0) else Option.none
    let some c := lower? | return ← fail
    let cS ← outer.withContext <| Term.exprToSyntax c
    -- a hypothesis that decides the test
    let decided? ← outer.withContext do
      let tT ← mkEq b (mkConst ``Bool.true)
      let tF ← mkEq b (mkConst ``Bool.false)
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        if ← withNewMCtxDepth (isDefEq ty tT) then return some (true, d.fvarId)
        if ← withNewMCtxDepth (isDefEq ty tF) then return some (false, d.fvarId)
      return Option.none
    if decidedOnly && decided?.isNone then return ← fail
    let mut out : List MVarId := []
    -- the loop runs: its start is `ofNat (min x0.natVal m)`
    setGoals [gp]
    match decided? with
    | some (false, h) =>
      let hS ← gp.withContext <| Term.exprToSyntax (mkFVar h)
      evalTactic (← `(tactic| exact absurd (($hb).symm.trans $hS) (by decide)))
    | _ =>
      evalTactic (← `(tactic| rw [show $x0S = F64.ofNat (Min.min (F64.natVal $x0S) $mS) from
        StrictTS.F64.floor_min_eq_ofNat_min (c := $cS) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
          $hb]))
      out := out ++ (← getGoals)
    -- the loop runs no iteration; nor do the other loops that the same test stops
    setGoals [gn]
    match decided? with
    | some (true, h) =>
      let hS ← gn.withContext <| Term.exprToSyntax (mkFVar h)
      evalTactic (← `(tactic| exact absurd (($hS).symm.trans $hb) (by decide)))
    | _ =>
      evalTactic (← `(tactic| rw [$hz:ident]))
      if decided?.isNone then
        for _ in [0:4] do
          if (← getGoals).isEmpty then break
          match ← startSplit hyps (decidedOnly := true) with
          | .none => break
          | _ => pure ()
        unless (← getGoals).isEmpty do
          try evalTactic (← `(tactic| simp [ts_sym, $hyps,*])) catch _ => pure ()
        unless (← getGoals).isEmpty do return ← fail
      out := out ++ (← getGoals)
    setGoals (out ++ rest)
    return if decided? matches some (false, _) then .zero else .runs
  catch _ => fail

/-- The experimental summary of loops that write two cells (off: the iteration does not close yet). -/
def twoCells : Bool := false


elab_rules : tactic
  | `(tactic| ts_summarize $[[$ls?,*]]? $[$xs?]?) => do
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := match ls? with
    | some ls => ls.getElems
    | none => #[]
  -- the call lemmas of the (non-recursive) functions that the first loop's body calls
  let lemmas ← withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    let loops := #[``evalForOf, ``evalLoop, ``evalForOfStr, ``evalForOfMap, ``evalForOfSet]
    match goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && loops.any (e.getArg! 2).isAppOf) with
    | some e => return lemmas ++ (← Summarize.calleeLemmas (e.getArg! 2))
    | none => return lemmas
  let saved ← saveState
  -- the first loop in the goal: a counted loop (`evalLoop`), a `for … of` loop over an array, or
  -- one over a string, map or set
  let firstFn ← withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    let loops := #[``evalForOf, ``evalLoop, ``evalForOfStr, ``evalForOfMap, ``evalForOfSet]
    let first := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && loops.any (e.getArg! 2).isAppOf)
    return first.map (fun e => (e.getArg! 2).getAppFn.constName!)
  let live? : Option LiveKind :=
    if firstFn == some ``evalForOfStr then some .str
    else if firstFn == some ``evalForOfMap then some .map
    else if firstFn == some ``evalForOfSet then some .set
    else none
  if let some kind := live? then
    let mut cell : Option Lean.Expr := none
    for round in [0:2] do
      let mut found := false
      -- each first without, then with `break`, then with `return`
      for (brk, ret) in [(false, false), (true, false), (false, true)] do
        saved.restore
        match ← summarizeLiveAttempt kind cell lemmas brk ret with
        | .done => return
        | .notNext => continue
        | .stuck g locals =>
          if round == 0 && cell.isNone then
            let tgt ← instantiateMVars (← g.getType)
            let cells ← g.withContext <| writtenCells tgt locals
            match cells.toList with
            | [K] => cell := some K; found := true
            | [] => throwError "ts_summarize: the body does not complete normally (with the world unchanged \
                or one cell written) on a symbolic state; remaining goal:\n{← ppGoal g}"
            | ks => throwError "ts_summarize: the body writes {ks.length} cells ({ks}); only one is \
                supported; remaining goal:\n{← ppGoal g}"
            break
          else
            throwError "ts_summarize: the body does not complete normally on a symbolic state; \
              remaining goal:\n{← ppGoal g}"
      unless found do break
    saved.restore
    throwError "ts_summarize: an iteration of the loop may end with throw (or a labelled break, or both \
      break and return)"
  let counted := firstFn == some ``evalLoop
  -- a backwards counted loop (`i--`)
  let down ← if counted then withMainContext do
      let goal ← instantiateMVars (← getMainTarget)
      let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop)
        | return false
      Summarize.isDecStep ((e.getArg! 2).getArg! 7)
    else pure false
  -- a counted `while` loop (`while (i < n) { …; i++ }`): the step block is empty
  let whileUp ← if counted then withMainContext do
      let goal ← instantiateMVars (← getMainTarget)
      let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop)
        | return false
      let step ← whnfR ((e.getArg! 2).getArg! 7)
      return step.isAppOf ``Block.nil && (← Summarize.lastIncSlot ((e.getArg! 2).getArg! 6)).isSome
    else pure false
  -- a backwards `while` loop (`while (i >= c) { …; i-- }`)
  let whileDown ← if counted && !whileUp then withMainContext do
      let goal ← instantiateMVars (← getMainTarget)
      let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop)
        | return false
      let step ← whnfR ((e.getArg! 2).getArg! 7)
      return step.isAppOf ``Block.nil && (← Summarize.lastDecSlot ((e.getArg! 2).getArg! 6)).isSome
    else pure false
  -- a backwards loop from a computed start: split on its condition at the start
  if whileDown || down then
    let hyps := (← heapHyps) ++ (← heapNeFacts) ++ lemmas
    match ← startSplit hyps with
    | .none => pure ()
    | .zero => return
    | .runs =>
      try
        evalTactic (← `(tactic| ts_summarize [$lemmas,*]))
        return
      catch ex =>
        saved.restore
        throw ex
  if whileDown then
    let mut cell : Option Lean.Expr := none
    for round in [0:2] do
      saved.restore
      match ← summarizeDownAttempt cell lemmas (whileMode := true) with
      | .done => return
      | .notNext => throwError "ts_summarize: an iteration of the while loop may end with \
          break/return/throw (only counted `while` loops without exits are supported)"
      | .stuck g locals =>
        if round == 0 then
          let tgt ← instantiateMVars (← g.getType)
          let cells ← g.withContext <| writtenCells tgt locals
          match cells.toList with
          | [K] => cell := some K
          | _ => throwError "ts_summarize: the body of the while loop does not complete normally (with \
              the counter stepped last, and the world unchanged or one cell written) on a symbolic state; \
              remaining goal:\n{← ppGoal g}"
        else
          throwError "ts_summarize: the body of the while loop does not complete normally on a symbolic \
            state; remaining goal:\n{← ppGoal g}"
    return
  if whileUp then
    let mut cell : Option Lean.Expr := none
    for round in [0:2] do
      saved.restore
      match ← summarizeWhileUpAttempt cell lemmas with
      | .done => return
      | .notNext => throwError "ts_summarize: an iteration of the while loop may end with \
          break/return/throw (only counted `while` loops without exits are supported)"
      | .stuck g locals =>
        if round == 0 then
          let tgt ← instantiateMVars (← g.getType)
          let cells ← g.withContext <| writtenCells tgt locals
          match cells.toList with
          | [K] => cell := some K
          | _ => throwError "ts_summarize: the body of the while loop does not complete normally (with \
              the counter stepped last, and the world unchanged or one cell written) on a symbolic state; \
              remaining goal:\n{← ppGoal g}"
        else
          throwError "ts_summarize: the body of the while loop does not complete normally on a symbolic \
            state; remaining goal:\n{← ppGoal g}"
    return
  if down then
    let mut cell : Option Lean.Expr := none
    for round in [0:2] do
      -- every mode first; a body stuck on a written cell is retried with that cell
      let mut stuck : Option (Array Lean.Expr × MessageData) := none
      for (brk, ret, retw) in [(false, false, false), (false, true, false), (true, false, false), (false, false, true)] do
        saved.restore
        match ← summarizeDownAttempt cell lemmas ret brk retw with
        | .done => return
        | .notNext => continue
        | .stuck g locals =>
          if stuck.isNone then
            let tgt ← instantiateMVars (← g.getType)
            let cells ← g.withContext <| writtenCells tgt locals
            stuck := some (cells, m!"{← ppGoal g}")
      match stuck with
      | none => break
      | some (cells, msg) =>
        if round == 0 && cell.isNone then
          match cells.toList with
          | [K] => cell := some K
          | [] => throwError "ts_summarize: the body of the backwards loop does not complete normally \
              (with the world unchanged or one cell written) on a symbolic state; remaining goal:\n{msg}"
          | ks => throwError "ts_summarize: the body writes {ks.length} cells ({ks}); only one is \
              supported; remaining goal:\n{msg}"
        else
          throwError "ts_summarize: the body of the backwards loop does not complete normally on a \
            symbolic state; remaining goal:\n{msg}"
    saved.restore
    throwError "ts_summarize: an iteration of the backwards loop may end with throw (or a labelled break, \
      or both break and return)"
  if counted then
    -- with a written array cell: as it is, then as a cell of fixed size (an in-place update of
    -- the array whose length the condition reads)
    -- (the addresses of the arrays whose length the condition reads: when the loop writes one
    -- of them, the fixed-size summary first)
    let lengthAddrs ← withMainContext do
      let goal ← instantiateMVars (← getMainTarget)
      let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop)
        | return #[]
      let args := (e.getArg! 2).getAppArgs
      let spine ← Summarize.ctxSpine args[3]!
      let comps ← Summarize.envComps args[8]! spine.size
      let found ← IO.mkRef (#[] : Array Lean.Expr)
      Meta.forEachExpr args[5]! fun sub => do
        if sub.isAppOf ``Expr.builtin && sub.getAppNumArgs ≥ 2 &&
            (sub.getArg! (sub.getAppNumArgs - 2)).isAppOf ``Builtin.arrLength then
          let as ← whnfR (sub.getArg! (sub.getAppNumArgs - 1))
          if as.isAppOf ``Args.cons && as.getAppNumArgs ≥ 2 then
            let x ← whnfR (as.getArg! (as.getAppNumArgs - 2))
            if x.isAppOf ``Expr.var then
              if let some k ← Summarize.varPos x.appArg! then
                if let some cv := comps[k]? then
                  let cv ← whnfR cv
                  if cv.isAppOf ``Val.arr then found.modify (·.push cv.appArg!)
      found.get
    let countedOrSized (cell : Option Lean.Expr) : TacticM Attempt := do
      let s ← saveState
      let readsWritten := match cell with
        | some K => K.isAppOfArity ``Prod.mk 4 && lengthAddrs.contains (K.getArg! 3)
        | none => false
      if readsWritten then
        try
          if let .done ← summarizeCountedAttempt cell lemmas (sized := true) then return .done
        catch _ => pure ()
        s.restore
      let r ← try summarizeCountedAttempt cell lemmas
        catch ex =>
          if cell.isNone then throw ex
          s.restore
          try return ← summarizeCountedAttempt cell lemmas (sized := true)
          catch _ =>
            s.restore
            throw ex
      match r with
      | .stuck .. =>
        if cell.isNone then return r
        let s2 ← saveState
        s.restore
        try
          match ← summarizeCountedAttempt cell lemmas (sized := true) with
          | .done => return .done
          | _ => s2.restore; return r
        catch _ =>
          s2.restore
          return r
      | _ => return r
    let mut cell : Option Lean.Expr := none
    for round in [0:2] do
      saved.restore
      match ← countedOrSized cell with
      | .done => return
      | .notNext =>
        -- an iteration may `return` or `break`
        saved.restore
        match ← summarizeCountedAttempt cell lemmas (ret := true) with
        | .done => return
        | _ =>
          saved.restore
          match ← summarizeCountedAttempt cell lemmas (brk := true) with
          | .done => return
          | _ => throwError "ts_summarize: an iteration of the counted loop may end with \
              throw (or a labelled break, or both break and return)"
      | .stuck g locals =>
        if round == 0 then
          let tgt ← instantiateMVars (← g.getType)
          let cells ← g.withContext <| writtenCells tgt locals
          match cells.toList with
          | [K] => cell := some K
          | [] => throwError "ts_summarize: the body of the counted loop does not complete normally \
              (with the world unchanged or one cell written) on a symbolic state; remaining goal:\n{← ppGoal g}"
          | ks => throwError "ts_summarize: the body writes {ks.length} cells ({ks}); only one is \
              supported; remaining goal:\n{← ppGoal g}"
        else
          throwError "ts_summarize: the body of the counted loop does not complete normally on a \
            symbolic state; remaining goal:\n{← ppGoal g}"
    return
  -- world unchanged; one or two written cells; each first without, then with `break`, then
  -- with `return`
  let mut cell : Option Lean.Expr := none
  let mut cell2 : Option Lean.Expr := none
  let mut diag : MessageData := m!""
  for round in [0:2] do
    for (brk, ret) in [(false, false), (true, false), (false, true)] do
      saved.restore
      match ← summarizeAttempt xs? cell brk lemmas cell2 ret with
      | .done => return
      | .notNext => continue
      | .stuck g locals =>
        if round == 0 && cell.isNone then
          let tgt ← instantiateMVars (← g.getType)
          let cells ← g.withContext <| writtenCells tgt locals
          diag := m!"{← ppGoal g}"
          match cells.toList with
          | [K] => cell := some K
          -- two written cells: the pair summary (`cell2`) is experimental and off
          | [K1, K2] =>
            if twoCells then
              cell := some K1
              cell2 := some K2
            else
              throwError "ts_summarize: the body writes 2 cells ({K1}, {K2}); only one is supported; \
                remaining goal:\n{diag}"
          | [] => throwError "ts_summarize: the body does not complete normally (with the world unchanged \
              or one cell written) on a symbolic state; remaining goal:\n{diag}"
          | ks => throwError "ts_summarize: the body writes {ks.length} cells ({ks}); only one is \
              supported; remaining goal:\n{diag}"
          break
        else
          let two := if cell2.isSome then " (two written cells: their joint summary is experimental)" else ""
          throwError "ts_summarize: the body does not complete normally on a symbolic state{two}; \
            remaining goal:\n{← ppGoal g}"
  saved.restore
  throwError "ts_summarize: an iteration may end with `throw` (or a labelled break, or both `break` \
    and `return`)"

end StrictTS


namespace StrictTS

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| ts_callbacks $[[$ls?,*]]? $[$xs?]?) => do
  -- (no array method with a callback in the goal: fail at once)
  let anyCb ← withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    let cbs := #[``Builtin.arrFilter, ``Builtin.arrSome, ``Builtin.arrEvery, ``Builtin.arrFind,
      ``Builtin.arrFindIndex, ``Builtin.arrFindLast, ``Builtin.arrFindLastIndex, ``Builtin.arrReduce,
      ``Builtin.arrMap, ``Builtin.arrForEach, ``Builtin.arrSort]
    return (goal.find? fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalBuiltin &&
      (e.getArg! 2).getAppNumArgs ≥ 6 && cbs.any (((e.getArg! 2).getArg! 5).isAppOf ·)).isSome
  unless anyCb do
    throwError "ts_callbacks: no call of an array method with a callback (evalBuiltin) in the goal"
  -- facts that tell apart the cells in the goal (a read past the fresh `filter` result array)
  let neFacts ← heapNeFacts
  withMainContext do
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := (match ls? with
    | some ls => ls.getElems
    | none => #[]) ++ neFacts
  let goal ← instantiateMVars (← getMainTarget)
  let preds : Array (Name × Name) := #[(``Builtin.arrFilter, ``StrictTS.arrFilter_pure'),
    (``Builtin.arrSome, ``StrictTS.arrSome_pure'), (``Builtin.arrEvery, ``StrictTS.arrEvery_pure'),
    (``Builtin.arrFind, ``StrictTS.arrFind_pure'), (``Builtin.arrFindIndex, ``StrictTS.arrFindIndex_pure'),
    (``Builtin.arrFindLast, ``StrictTS.arrFindLast_pure'),
    (``Builtin.arrFindLastIndex, ``StrictTS.arrFindLastIndex_pure')]
  let isCb (b : Lean.Expr) := b.isAppOf ``Builtin.arrReduce || b.isAppOf ``Builtin.arrMap ||
    b.isAppOf ``Builtin.arrForEach || b.isAppOf ``Builtin.arrSort || preds.any (b.isAppOf ·.1)
  -- (a call under a binder, e.g. inside a comparator's lambda or a stuck `match`'s case, has
  -- loose bound variables: not a call of the goal)
  let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalBuiltin &&
      isCb ((e.getArg! 2).getArg! 5) && !e.hasLooseBVars)
    | throwError "ts_callbacks: no call of an array method with a callback (evalBuiltin) in the goal"
  let call := e.getArg! 2
  let w0 := e.getArg! 3
  let args := call.getAppArgs
  -- evalBuiltin {TT} I P {args} {t} b vs
  let TT := args[0]!
  let b := args[5]!
  let vsE ← whnfR args[6]!
  let comps : Array Lean.Expr := Id.run do
    let mut out := #[]
    let mut cur := vsE
    for _ in [0:3] do
      if cur.isAppOfArity ``Vals.cons 5 then
        out := out.push (cur.getArg! 3)
        cur := cur.getArg! 4
    return out
  let arrV ← whnfR comps[0]!
  unless arrV.isAppOf ``Val.arr do throwError "ts_callbacks: the array is not a literal reference: {arrV}"
  let a := arrV.appArg!
  let bArgs := b.getAppArgs
  let t := bArgs[0]!
  let valT (ty : Lean.Expr) := mkApp2 (mkConst ``Val) TT ty
  let xs ← match xs? with
    | some xs => pure xs
    | none => do Term.exprToSyntax (← mkFreshExprMVar (mkApp (mkConst ``Array [0]) (valT t)))
  let I ← Term.exprToSyntax args[1]!
  let P ← Term.exprToSyntax args[2]!
  let aS ← Term.exprToSyntax a
  let fS ← Term.exprToSyntax comps[1]!
  let wS ← Term.exprToSyntax w0
  let hcb := mkIdent `hcb
  let isReduce := b.isAppOf ``Builtin.arrReduce
  let isSort := b.isAppOf ``Builtin.arrSort
  -- the callback's meaning, read off by unification (none for `forEach`)
  let g? ← if isReduce then
      let u := bArgs[1]!
      some <$> mkFreshExprMVar (← mkArrow (valT u) (← mkArrow (valT t) (valT u)))
    else if isSort then
      some <$> mkFreshExprMVar (← mkArrow (valT t) (← mkArrow (valT t) (valT (mkConst ``Ty.num))))
    else if b.isAppOf ``Builtin.arrMap then
      let u := bArgs[1]!
      some <$> mkFreshExprMVar (← mkArrow (valT t) (valT u))
    else if b.isAppOf ``Builtin.arrForEach then pure none
    else some <$> mkFreshExprMVar (← mkArrow (valT t) (valT (mkConst ``Ty.bool)))
  -- (made before the saved state: their terms must survive a restore; the call lemmas of the non-recursive functions that the callback calls)
  let lemmas := lemmas ++ (← Summarize.calleeLemmas comps[1]!)
  let a01 := #[← `(Lean.Parser.Tactic.simpLemma| Vals.a0_cons), ← `(Lean.Parser.Tactic.simpLemma| Vals.a1_cons)]
    ++ (← heapHyps) ++ lemmas
  let a0 := #[← `(Lean.Parser.Tactic.simpLemma| Vals.a0_cons)] ++ (← heapHyps) ++ lemmas
  -- (the state to come back to when the callback is pure only in the world of the call)
  let saved ← saveState
  match g? with
  | none =>
    evalTactic (← `(tactic| have $hcb := StrictTS.arrForEach_pure' $I $P $aS $xs $fS ?hf $wS ?hw))
  | some g =>
    let gS ← Term.exprToSyntax g
    if isReduce then
      let initS ← Term.exprToSyntax comps[2]!
      evalTactic (← `(tactic| have $hcb := StrictTS.arrReduce_pure' $I $P $aS $xs $fS $initS $gS ?hf $wS ?hw))
    else if isSort then
      evalTactic (← `(tactic| have $hcb := StrictTS.arrSort_pure' $I $P $aS $xs $fS $gS ?hf $wS ?hw))
    else if b.isAppOf ``Builtin.arrMap then
      evalTactic (← `(tactic| have $hcb := StrictTS.arrMap_pure' $I $P $aS $xs $fS $gS ?hf $wS ?hw ?ha))
    else if b.isAppOf ``Builtin.arrFilter then
      evalTactic (← `(tactic| have $hcb := StrictTS.arrFilter_pure' $I $P $aS $xs $fS $gS ?hf $wS ?hw ?ha))
    else
      let some (_, lem) := preds.find? (b.isAppOf ·.1)
        | throwError "ts_callbacks: internal error (unknown method)"
      let lemI := mkIdent lem
      evalTactic (← `(tactic| have $hcb := $lemI $I $P $aS $xs $fS $gS ?hf $wS ?hw))
  let mut gls ← getGoals
  let some hf0 := (← gls.filterM fun g => return (← g.getTag).eraseMacroScopes == `hf).head?
    | throwError "ts_callbacks: internal error (no hf goal)"
  let mut hf := hf0
  setGoals [hf]
  -- (without error recovery: a callback that does not evaluate must fail here, not be admitted)
  try withoutRecover do
    if isReduce then
      evalTactic (← `(tactic| (
        intro vs w'
        match vs with
        | .cons acc (.cons x (.cons i (.cons arr .nil))) =>
          ts_merge [$a01,*])))
    else if isSort then
      evalTactic (← `(tactic| (
        intro vs w'
        match vs with
        | .cons x (.cons y .nil) =>
          ts_merge [$a01,*])))
    else
      evalTactic (← `(tactic| (
        intro vs w'
        match vs with
        | .cons x (.cons i (.cons arr .nil)) =>
          ts_merge [$a0,*])))
  catch _ => pure ()
  -- a callback that reads the heap (another array, a `Set`): pure in the world where the method
  -- calls it (`arrFilter_pureAt`, …)
  let atLem? : Option Name :=
    if b.isAppOf ``Builtin.arrFilter then some ``StrictTS.arrFilter_pureAt
    else if b.isAppOf ``Builtin.arrMap then some ``StrictTS.arrMap_pureAt
    else if b.isAppOf ``Builtin.arrSome then some ``StrictTS.arrSome_pureAt
    else if b.isAppOf ``Builtin.arrEvery then some ``StrictTS.arrEvery_pureAt
    else if b.isAppOf ``Builtin.arrFind then some ``StrictTS.arrFind_pureAt
    else if b.isAppOf ``Builtin.arrFindIndex then some ``StrictTS.arrFindIndex_pureAt
    else none
  unless (← getGoals).isEmpty do
    let some atLem := atLem?
      | throwError "ts_callbacks: the callback is not a pure function of its first arguments; \
          remaining goal:\n{← ppGoal (← getMainGoal)}"
    let stuck ← ppGoal (← getMainGoal)
    saved.restore
    let some g := g? | throwError "ts_callbacks: internal error (no callback meaning)"
    let gS ← Term.exprToSyntax g
    let lemI := mkIdent atLem
    if b.isAppOf ``Builtin.arrFilter || b.isAppOf ``Builtin.arrMap then
      evalTactic (← `(tactic| have $hcb := $lemI $I $P $aS $xs $fS $gS $wS ?hf ?hw ?ha))
    else
      evalTactic (← `(tactic| have $hcb := $lemI $I $P $aS $xs $fS $gS $wS ?hf ?hw))
    gls ← getGoals
    let some hf1 := (← gls.filterM fun g => return (← g.getTag).eraseMacroScopes == `hf).head?
      | throwError "ts_callbacks: internal error (no hf goal)"
    hf := hf1
    setGoals [hf]
    -- (the world of the call may hold a fresh array: the facts that tell its address apart)
    let atFacts ← heapNeFacts
    let a0' := a0 ++ atFacts
    let mut why := m!""
    try withoutRecover do
      evalTactic (← `(tactic| (
        intro vs
        match vs with
        | .cons x (.cons i (.cons arr .nil)) =>
          ts_merge [$a0',*])))
    catch ex => why := ex.toMessageData
    unless (← getGoals).isEmpty do
      throwError "ts_callbacks: the callback is not a pure function of its first arguments (also in the \
        world of the call: {why}); remaining goal:\n{stuck}"
  if let some g := g? then
    unless ← g.mvarId!.isAssigned do throwError "ts_callbacks: could not read off the callback"
  setGoals (gls.filter (· != hf))
  evalTactic (← `(tactic| rw [$hcb:ident]))
  evalTactic (← `(tactic| clear $hcb:ident))
  let gls2 ← getGoals
  -- (the lemmas carry the heap facts: this call's, or a nested call's enclosing call's)
  let closeLs := lemmas ++ (← heapHyps)
  let mut rest := #[]
  for g in gls2 do
    let tag := (← g.getTag).eraseMacroScopes
    if tag == `hw || tag == `ha then
      setGoals [g]
      try evalTactic (← `(tactic| first | assumption | (simp only [ts_sym]; assumption) | (simp only [ts_sym]; rfl) |
        (simp only [ts_sym, $closeLs,*]; rfl) | (simp [ts_sym, *]; done) | omega | (dsimp only; omega)))
      catch _ => rest := rest.push g
      unless (← getGoals).isEmpty do rest := rest.push g
    else rest := rest.push g
  setGoals rest.toList
  unless (← getGoals).isEmpty do clearNeFacts

end StrictTS
