import CIR.Semantics.Eval

/-!
  Total-correctness weakest preconditions.

  `r.holds Q` says that the computation `r` terminates without undefined
  behaviour and its result satisfies `Q`. Because `Res.holds_bind` is an
  equivalence, `simp` turns a monadic computation into nested `holds`
  obligations, which is how straight-line code is executed symbolically.
  Loops and calls are handled by the rules in `CIR.Logic.Rules`.
-/

namespace CIR

/-- `r` terminates without undefined behaviour with a result satisfying `Q`. -/
def Res.holds {α : Type} (r : Res α) (Q : α → Prop) : Prop :=
  match r with
  | .ok a => Q a
  | _ => False

namespace Res

variable {α β : Type}

@[simp] theorem holds_ok {a : α} {Q : α → Prop} : (Res.ok a).holds Q ↔ Q a := Iff.rfl
@[simp] theorem holds_ub {m : String} {Q : α → Prop} : (Res.ub m : Res α).holds Q ↔ False := Iff.rfl
@[simp] theorem holds_div {Q : α → Prop} : (Res.div : Res α).holds Q ↔ False := Iff.rfl

@[simp] theorem holds_pure {a : α} {Q : α → Prop} : (pure a : Res α).holds Q ↔ Q a := Iff.rfl

@[simp] theorem holds_bind {x : Res α} {f : α → Res β} {Q : β → Prop} :
    (x >>= f).holds Q ↔ x.holds (fun a => (f a).holds Q) := by
  cases x <;> rfl

@[simp] theorem holds_ofOption {m : String} {o : Option α} {Q : α → Prop} :
    (Res.ofOption m o).holds Q ↔ ∃ a, o = some a ∧ Q a := by
  cases o <;> simp [ofOption]

theorem holds_mono {x : Res α} {P Q : α → Prop} (h : x.holds P) (hPQ : ∀ a, P a → Q a) :
    x.holds Q := by
  cases x <;> simp_all [holds]

theorem holds_ok_iff {x : Res α} {Q : α → Prop} : x.holds Q ↔ ∃ a, x = .ok a ∧ Q a := by
  cases x <;> simp [holds]

theorem holds_ite {c : Prop} [Decidable c] {x y : Res α} {Q : α → Prop} :
    (if c then x else y).holds Q ↔ (c → x.holds Q) ∧ (¬c → y.holds Q) := by
  by_cases h : c <;> simp [h]

end Res

/-! ### Judgements -/

/-- Calling `sym` terminates without undefined behaviour and its outcome
(`Exit.ret`/`Exit.exn` and the final memory) satisfies `Q`. -/
def Calls (ctx : Ctx) (sym : String) (args : List Val) (m : Mem) (Q : Exit → Mem → Prop) : Prop :=
  (evalCall ctx sym args m).holds fun r => Q r.1 r.2

/-- A function returns normally (no exception, no `exit`) with `post` holding. -/
def Returns (ctx : Ctx) (sym : String) (args : List Val) (m : Mem)
    (post : Option Val → Mem → Prop) : Prop :=
  Calls ctx sym args m fun e m' => match e with
    | .ret v => post v m'
    | _ => False

/-- A call that ends the program (`exit(n)`) does not return. -/
theorem Calls.not_returns {ctx : Ctx} {sym : String} {args : List Val} {m : Mem} {n : Int}
    {post : Option Val → Mem → Prop} (h : Calls ctx sym args m fun e _ => e = .halt n) :
    ¬ Returns ctx sym args m post := by
  unfold Returns Calls at *
  intro hr
  obtain ⟨⟨e, m'⟩, he, hq⟩ := Res.holds_ok_iff.mp h
  rw [he] at hr
  dsimp only at hq
  subst hq
  exact hr

/-! ### Function specifications and the frame -/

/-- The callee changed only the blocks `mods` among those existing before the
call (`m`), and did not shrink the block counter. Its own stack blocks are
gone (they were erased at its exit). -/
def Frame (m m' : Mem) (mods : List Nat) : Prop :=
  m.next ≤ m'.next ∧ ∀ b, b ∉ mods → b < m.next → m'.blocks b = m.blocks b

/-- Call rule: use a proved specification of the callee instead of its body. -/
theorem holds_call_spec {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    {post : Option Val → Mem → Prop} {K : Exit × Mem → Prop}
    (hspec : Returns ctx sym args m post) (hk : ∀ v m', post v m' → K (.ret v, m')) :
    (evalCall ctx sym args m).holds K := by
  unfold Returns Calls at hspec
  apply Res.holds_mono hspec
  rintro ⟨e, m'⟩ h
  cases e with
  | ret v => exact hk v m' h
  | _ => exact absurd h id

end CIR
