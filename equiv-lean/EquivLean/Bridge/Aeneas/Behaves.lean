import Aeneas
import EquivLean.Core.Sim

/-!
# Aeneas (Rust) bridge: outcome semantics

Aeneas translates a Rust function to a Lean function into `Aeneas.Std.Result α`, an
interaction tree with three shapes: `ok a` (normal return), `fail e` (a panic: integer
overflow, division by zero, out-of-bounds index, failed assertion, …) and `div` (divergence).

* Observable outcomes are `Except Error α`: `.ok a` for a return, `.error e` for a panic with
  reason `e`.  A panic is part of the behaviour of a Rust function, so equivalence proofs must
  match panics too (the same reason on the same inputs).
* `Safe c` means that `c` does not diverge (`safe_iff_ne_div`); every safe computation finishes
  with exactly one outcome (`Total`, `Det`).

`wp` of a Rust computation therefore is total correctness in which panics are outcomes.
Aeneas' own judgement `spec c p` (`c ⦃ p ⦄`) is the special case that excludes panics
(`spec_iff_wp`).

The `@[simp]` lemmas below execute a computation symbolically: `bind` (`Std.bind` and the
typeclass `>>=`), `ite`/`dite`, `lift`, `massert`, slice and vector indexing, `Vec.push`, and
the checked scalar operations of Aeneas' standard library with *both* outcomes.  They are
derived from Aeneas' definitions, so a proof that uses them matches the panics of the
translated program exactly.  Each scalar operation comes in three forms:

* value form (`wp_UScalar_add_val`, …, the default `@[simp]` lemmas): the result is
  `UScalar.ofNatCore (x.val + y.val) _`, so the leaves are linear arithmetic on `.val`;
* bit-vector form (`wp_UScalar_add`, …): the result is `⟨x.bv + y.bv⟩`;
* bit-vector conditions (`wp_UScalar_add_bvc`, …): overflow tests as `BitVec.uaddOverflow`
  etc., so that a symbolically executed goal is a `bv_decide` problem.
-/

open Aeneas Aeneas.Std

namespace EquivLean.Aeneas

universe u v

/-- The computation with outcome `o`. -/
def ofExcept {α : Type u} : Except Error α → Result α
  | .ok a => Result.ok a
  | .error e => Result.fail e

/-- Rust computations: outcomes are results and panics, divergence is unsafe. -/
instance instBehavesResult (α : Type u) : Behaves (Result α) (Except Error α) where
  Runs c o := c = ofExcept o
  Safe c := ∃ o, c = ofExcept o

section basic
variable {α : Type u}

theorem runs_iff {c : Result α} {o : Except Error α} : Runs c o ↔ c = ofExcept o := Iff.rfl

theorem safe_iff {c : Result α} : Safe c ↔ ∃ o, c = ofExcept o := Iff.rfl

@[simp] theorem ofExcept_ok (a : α) : ofExcept (.ok a : Except Error α) = Result.ok a := rfl

@[simp] theorem ofExcept_error (e : Error) : ofExcept (.error e : Except Error α) = Result.fail e :=
  rfl

theorem ofExcept_injective : Function.Injective (ofExcept (α := α)) := by
  intro o₁ o₂ h
  cases o₁ <;> cases o₂ <;> simp_all [ofExcept]

theorem ofExcept_ne_div (o : Except Error α) : ofExcept o ≠ Result.div := by
  cases o <;> simp [ofExcept]

instance (α : Type u) : Behaves.Total (Result α) := ⟨fun _ ⟨o, h⟩ => ⟨o, h⟩⟩

instance (α : Type u) : Behaves.Det (Result α) :=
  ⟨fun _ _ _ h₁ h₂ => ofExcept_injective (h₁.symm.trans h₂)⟩

/-- Every Rust computation returns, panics, or diverges. -/
theorem result_trichotomy (x : Result α) :
    (∃ a, x = Result.ok a) ∨ (∃ e, x = Result.fail e) ∨ x = Result.div := by
  cases x with
  | ret a => exact .inl ⟨a, rfl⟩
  | vis i k =>
    cases i with
    | fail e =>
      refine .inr (.inl ⟨e, ?_⟩)
      rw [Result.fail_eq_vis]
      congr
      funext z
      exact PEmpty.elim z
  | div => exact .inr (.inr rfl)

/-- A Rust computation is safe iff it does not diverge. -/
theorem safe_iff_ne_div {c : Result α} : Safe c ↔ c ≠ Result.div := by
  constructor
  · rintro ⟨o, rfl⟩
    exact ofExcept_ne_div o
  · intro h
    rcases result_trichotomy c with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl
    · exact ⟨.ok a, rfl⟩
    · exact ⟨.error e, rfl⟩
    · exact absurd rfl h

@[simp] theorem safe_ok (a : α) : Safe (Result.ok a) := ⟨.ok a, rfl⟩

@[simp] theorem safe_fail (e : Error) : Safe (Result.fail e : Result α) := ⟨.error e, rfl⟩

@[simp] theorem not_safe_div : ¬ Safe (Result.div : Result α) := fun h => safe_iff_ne_div.1 h rfl

@[simp] theorem runs_ok_iff (a : α) (o : Except Error α) : Runs (Result.ok a) o ↔ o = .ok a := by
  rw [runs_iff]
  constructor
  · intro h; exact ofExcept_injective (show ofExcept o = ofExcept (.ok a) from h.symm)
  · rintro rfl; rfl

@[simp] theorem runs_fail_iff (e : Error) (o : Except Error α) :
    Runs (Result.fail e : Result α) o ↔ o = .error e := by
  rw [runs_iff]
  constructor
  · intro h; exact ofExcept_injective (show ofExcept o = ofExcept (.error e) from h.symm)
  · rintro rfl; rfl

@[simp] theorem not_runs_div (o : Except Error α) : ¬ Runs (Result.div : Result α) o :=
  fun h => ofExcept_ne_div o (runs_iff.1 h).symm

theorem wp_ofExcept (o : Except Error α) (Q : Except Error α → Prop) :
    wp (ofExcept o) Q ↔ Q o :=
  wp_iff_of_runs (safe_iff.2 ⟨o, rfl⟩) rfl

@[simp] theorem wp_ok (a : α) (Q : Except Error α → Prop) : wp (Result.ok a) Q ↔ Q (.ok a) :=
  wp_ofExcept (.ok a) Q

@[simp] theorem wp_fail (e : Error) (Q : Except Error α → Prop) :
    wp (Result.fail e : Result α) Q ↔ Q (.error e) :=
  wp_ofExcept (.error e) Q

@[simp] theorem wp_div (Q : Except Error α → Prop) : wp (Result.div : Result α) Q ↔ False :=
  ⟨fun h => absurd rfl (safe_iff_ne_div.1 h.1), False.elim⟩

@[simp] theorem wp_pure (a : α) (Q : Except Error α → Prop) :
    wp (pure a : Result α) Q ↔ Q (.ok a) :=
  wp_ok a Q

@[simp] theorem wp_lift (a : α) (Q : Except Error α → Prop) : wp (lift a) Q ↔ Q (.ok a) :=
  wp_ok a Q

/-- `wp` of a computation in terms of its three shapes. -/
theorem wp_iff (c : Result α) (Q : Except Error α → Prop) :
    wp c Q ↔ (∃ a, c = Result.ok a ∧ Q (.ok a)) ∨ (∃ e, c = Result.fail e ∧ Q (.error e)) := by
  rcases result_trichotomy c with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl <;> simp

end basic

/-! ## Control flow -/

section control
variable {α : Type u} {β : Type v}

@[simp] theorem wp_bind (x : Result α) (f : α → Result β) (Q : Except Error β → Prop) :
    wp (Std.bind x f) Q ↔ wp x (fun o => match o with
      | .ok a => wp (f a) Q
      | .error e => Q (.error e)) := by
  rcases result_trichotomy x with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl <;> simp

@[simp] theorem wp_bind_tc {α β : Type u} (x : Result α) (f : α → Result β)
    (Q : Except Error β → Prop) :
    wp (x >>= f) Q ↔ wp x (fun o => match o with
      | .ok a => wp (f a) Q
      | .error e => Q (.error e)) :=
  wp_bind x f Q

@[simp] theorem wp_ite {c : Prop} [Decidable c] (t e : Result α) (Q : Except Error α → Prop) :
    wp (if c then t else e) Q ↔ if c then wp t Q else wp e Q := by
  split <;> rfl

@[simp] theorem wp_dite {c : Prop} [Decidable c] (t : c → Result α) (e : ¬ c → Result α)
    (Q : Except Error α → Prop) :
    wp (if h : c then t h else e h) Q ↔ if h : c then wp (t h) Q else wp (e h) Q := by
  split <;> rfl

@[simp] theorem wp_massert (b : Prop) [Decidable b] (Q : Except Error Unit → Prop) :
    wp (massert b) Q ↔ if b then Q (.ok ()) else Q (.error .assertionFailure) := by
  unfold massert; split <;> simp

@[simp] theorem wp_ofOption (x : Option α) (e : Error) (Q : Except Error α → Prop) :
    wp (Result.ofOption x e) Q ↔ match x with
      | some a => Q (.ok a)
      | none => Q (.error e) := by
  cases x <;> simp

end control

/-! ## Relational helpers

Two Rust computations are deterministic and total, so running the source first and then the
target ("self-composition") proves simulation in both directions. -/

section rel
variable {α : Type u} {β : Type v}

theorem sim_of_wp {t : Result α} {s : Result β} {R : Except Error α → Except Error β → Prop}
    (h : wp s (fun os => wp t (fun ot => R ot os))) : Sim R t s :=
  Sim.of_seq h

theorem equiv_of_wp {t : Result α} {s : Result β} {R : Except Error α → Except Error β → Prop}
    (h : wp s (fun os => wp t (fun ot => R ot os))) : Equiv R t s := by
  refine ⟨Sim.of_seq h, Sim.of_seq ?_⟩
  obtain ⟨os, hos, ht⟩ := wp_exists h
  obtain ⟨ot, hot, hR⟩ := wp_exists ht
  exact (wp_iff_of_runs ht.1 hot).2 ((wp_iff_of_runs h.1 hos).2 hR)

/-- A Rust computation against a pure Lean value (`pureVal`): simulation is a `wp`. -/
theorem sim_pureVal_iff {γ : Type v} {t : Result α} {a : γ} {R : Except Error α → γ → Prop} :
    Sim R t (pureVal a) ↔ wp t (fun ot => R ot a) :=
  sim_iff_of_runs (s := (pureVal a : Id γ)) trivial rfl

/-- … and so is equivalence (a Rust computation is deterministic and total). -/
theorem equiv_pureVal_iff {γ : Type v} {t : Result α} {a : γ} {R : Except Error α → γ → Prop} :
    Equiv R t (pureVal a) ↔ wp t (fun ot => R ot a) := by
  refine ⟨fun h => sim_pureVal_iff.1 h.1, fun h => ⟨sim_pureVal_iff.2 h, fun _ => ?_⟩⟩
  obtain ⟨ot, hot, hR⟩ := wp_exists h
  exact ⟨trivial, fun o ho => ⟨ot, hot, (show o = a from ho) ▸ hR⟩⟩

/-- One simulation and the safety of the source give equivalence (both sides are
deterministic and total). -/
theorem equiv_of_sim_of_safe {t : Result α} {s : Result β}
    {R : Except Error α → Except Error β → Prop} (h : Sim R t s) (hs : Safe s) :
    Equiv R t s := by
  refine ⟨h, fun _ => ⟨hs, fun os hos => ?_⟩⟩
  obtain ⟨hts, hrun⟩ := h hs
  obtain ⟨ot, hot⟩ := Behaves.Total.progress t hts
  obtain ⟨os', hos', hR⟩ := hrun ot hot
  exact ⟨ot, hot, (Behaves.Det.det s os' os hos' hos) ▸ hR⟩

/-- For Rust computations, equivalence with equal outcomes is equality: a proved
`Equiv (· = ·)` between two callees can be rewritten inside any caller. -/
theorem equiv_eq_iff {t s : Result α} : Equiv (· = ·) t s ↔ t = s := by
  constructor
  · intro h
    rcases result_trichotomy s with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl
    · obtain ⟨ht, hrun⟩ := h.1 (safe_ok a)
      obtain ⟨o, ho⟩ := Behaves.Total.progress t ht
      obtain ⟨o', ho', he⟩ := hrun o ho
      rw [runs_ok_iff] at ho'
      subst ho' he
      exact ho
    · obtain ⟨ht, hrun⟩ := h.1 (safe_fail e)
      obtain ⟨o, ho⟩ := Behaves.Total.progress t ht
      obtain ⟨o', ho', he⟩ := hrun o ho
      rw [runs_fail_iff] at ho'
      subst ho' he
      exact ho
    · rcases result_trichotomy t with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl
      · exact absurd (h.2 (safe_ok a)).1 not_safe_div
      · exact absurd (h.2 (safe_fail e)).1 not_safe_div
      · rfl
  · rintro rfl
    exact Equiv.refl t

/-- Two computations with the same known outcome are equivalent. -/
theorem equiv_of_wp_eq {t s : Result α} {o : Except Error α} (ht : wp t (· = o))
    (hs : wp s (· = o)) : Equiv (· = ·) t s :=
  equiv_of_wp (wp_mono hs fun _ hos => wp_mono ht fun _ hot => hot.trans hos.symm)

end rel

/-! ## Slices -/

section slice
variable {α : Type u}

@[simp] theorem wp_Slice_index_usize (v : Slice α) (i : Usize) (Q : Except Error α → Prop) :
    wp (Slice.index_usize v i) Q ↔
      if h : i.val < v.val.length then Q (.ok (v.val[i.val]'h))
      else Q (.error .arrayOutOfBounds) := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  by_cases h : i.val < v.val.length
  · rw [List.getElem?_eq_getElem h, dite_eq_left h]
    exact wp_ok _ Q
  · rw [List.getElem?_eq_none (by omega), dite_eq_right h]
    exact wp_fail _ Q

end slice

/-! ## Vectors -/

section vec
variable {α : Type u}

@[simp] theorem wp_Vec_index_usize (v : alloc.vec.Vec α) (i : Usize) (Q : Except Error α → Prop) :
    wp (alloc.vec.Vec.index_usize v i) Q ↔
      if h : i.val < v.val.length then Q (.ok (v.val[i.val]'h))
      else Q (.error .arrayOutOfBounds) := by
  unfold alloc.vec.Vec.index_usize
  rw [alloc.vec.Vec.getElem?_Nat_eq]
  by_cases h : i.val < v.val.length
  · rw [List.getElem?_eq_getElem h, dite_eq_left h]
    exact wp_ok _ Q
  · rw [List.getElem?_eq_none (by omega), dite_eq_right h]
    exact wp_fail _ Q

/-- `push` panics (`maximumSizeExceeded`) when the length would exceed `usize::MAX`. -/
@[simp] theorem wp_Vec_push (v : alloc.vec.Vec α) (x : α) (Q : Except Error (alloc.vec.Vec α) → Prop) :
    wp (alloc.vec.Vec.push v x) Q ↔
      if h : v.val.length < Usize.max then
        Q (.ok (alloc.vec.Vec.from (v.val ++ [x]) (by simp; omega)))
      else Q (.error .maximumSizeExceeded) := by
  unfold alloc.vec.Vec.push
  have hU : U32.max ≤ Usize.max := by
    rcases Usize.bounds_eq with h | h <;> simp [h, U32.max_eq, U64.max_eq]
  by_cases h : v.val.length < Usize.max
  · rw [dite_eq_left (by simp; omega), dite_eq_left h, wp_ok]
    simp
  · rw [dite_eq_right (by simp; omega), dite_eq_right h, wp_fail]

end vec

/-! ## Aeneas' `spec` and `dspec` -/

section spec
variable {α : Type u}
open WP

/-- Aeneas' total-correctness judgement is `wp` with panics excluded. -/
theorem spec_iff_wp (c : Result α) (p : α → Prop) :
    spec c p ↔ wp c (fun o => ∃ a, o = .ok a ∧ p a) := by
  rcases result_trichotomy c with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl <;> simp

theorem spec_iff_wp' (c : Result α) (p : α → Prop) :
    spec c p ↔ wp c (fun o => match o with | .ok a => p a | .error _ => False) := by
  rcases result_trichotomy c with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl <;> simp

theorem wp_of_spec {c : Result α} {p : α → Prop} {Q : Except Error α → Prop} (h : spec c p)
    (hQ : ∀ a, p a → Q (.ok a)) : wp c Q :=
  wp_mono ((spec_iff_wp c p).1 h) fun _ ⟨a, he, ha⟩ => he ▸ hQ a ha

/-- Aeneas' partial-correctness judgement: divergence, or `spec`. -/
theorem dspec_iff (c : Result α) (p : α → Prop) :
    dspec c p ↔ c = Result.div ∨ spec c p := by
  rcases result_trichotomy c with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl <;> simp

theorem dspec_false_iff (c : Result α) : dspec c (fun _ => False) ↔ c = Result.div := by
  rcases result_trichotomy c with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl <;> simp

end spec

/-! ## Checked scalar arithmetic

Each lemma covers both outcomes of the operation, as defined by Aeneas' standard library
(`UScalar.add`, `UScalar.sub`, …).  The result value is stated on the bit-vector
representation (`⟨x.bv + y.bv⟩`, the wrapping result, which equals the mathematical result
in the non-overflow branch: see `EquivLean.Aeneas.UScalar.val_add_of_le` in `Corr.lean`). -/

section scalar
variable {uty : UScalarTy} {ity : IScalarTy}

theorem wp_UScalar_tryMk (n : Nat) (Q : Except Error (UScalar uty) → Prop) :
    wp (UScalar.tryMk uty n) Q ↔
      if h : n < 2 ^ uty.numBits then Q (.ok (UScalar.ofNatCore n h))
      else Q (.error .integerOverflow) := by
  unfold UScalar.tryMk UScalar.tryMkOpt
  by_cases h : n < 2 ^ uty.numBits <;> simp [h]

theorem wp_IScalar_tryMk (n : Int) (Q : Except Error (IScalar ity) → Prop) :
    wp (IScalar.tryMk ity n) Q ↔
      if h : -2 ^ (ity.numBits - 1) ≤ n ∧ n < 2 ^ (ity.numBits - 1) then
        Q (.ok (IScalar.ofIntCore n h))
      else Q (.error .integerOverflow) := by
  unfold IScalar.tryMk IScalar.tryMkOpt
  by_cases h : -2 ^ (ity.numBits - 1) ≤ n ∧ n < 2 ^ (ity.numBits - 1) <;> simp [h]

theorem UScalar.lt_pow_iff_le_max (n : Nat) : n < 2 ^ uty.numBits ↔ n ≤ UScalar.max uty := by
  have := Nat.one_le_two_pow (n := uty.numBits)
  rw [UScalar.max_def]; omega

theorem IScalar.inBounds_iff (n : Int) :
    (-2 ^ (ity.numBits - 1) ≤ n ∧ n < 2 ^ (ity.numBits - 1)) ↔
      IScalar.min ity ≤ n ∧ n ≤ IScalar.max ity := by
  rw [IScalar.min_def, IScalar.max_def]; omega

theorem UScalar.ofNatCore_eq_of_toNat {n : Nat} (h : n < 2 ^ uty.numBits)
    {b : BitVec uty.numBits} (hb : b.toNat = n) : UScalar.ofNatCore n h = ⟨b⟩ := by
  apply UScalar.eq_of_val_eq
  show n = b.toNat
  exact hb.symm

theorem IScalar.ofIntCore_eq_of_toInt {n : Int}
    (h : -2 ^ (ity.numBits - 1) ≤ n ∧ n < 2 ^ (ity.numBits - 1))
    {b : BitVec ity.numBits} (hb : b.toInt = n) : IScalar.ofIntCore n h = ⟨b⟩ := by
  apply IScalar.eq_of_val_eq
  rw [IScalar.ofInt_val_eq]
  exact hb.symm

theorem UScalar.add_def' (x y : UScalar uty) : x + y = UScalar.tryMk uty (x.val + y.val) := rfl
theorem UScalar.mul_def' (x y : UScalar uty) : x * y = UScalar.tryMk uty (x.val * y.val) := rfl
theorem IScalar.add_def' (x y : IScalar ity) : x + y = IScalar.tryMk ity (x.val + y.val) := rfl
theorem IScalar.sub_def' (x y : IScalar ity) : x - y = IScalar.tryMk ity (x.val - y.val) := rfl
theorem IScalar.mul_def' (x y : IScalar ity) : x * y = IScalar.tryMk ity (x.val * y.val) := rfl
theorem IScalar.neg_def' (x : IScalar ity) : -. x = IScalar.tryMk ity (- x.val) := rfl

theorem wp_UScalar_add (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x + y) Q ↔
      if x.val + y.val ≤ UScalar.max uty then Q (.ok ⟨x.bv + y.bv⟩)
      else Q (.error .integerOverflow) := by
  rw [UScalar.add_def', wp_UScalar_tryMk]
  by_cases h : x.val + y.val < 2 ^ uty.numBits
  · rw [dite_eq_left h, ite_eq_left ((UScalar.lt_pow_iff_le_max _).1 h),
      UScalar.ofNatCore_eq_of_toNat h (b := x.bv + y.bv)
        (by rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h)]
  · rw [dite_eq_right h, ite_eq_right (mt (UScalar.lt_pow_iff_le_max _).2 h)]

theorem wp_UScalar_sub (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x - y) Q ↔
      if y.val ≤ x.val then Q (.ok ⟨x.bv - y.bv⟩) else Q (.error .integerOverflow) := by
  change wp (UScalar.sub x y) Q ↔ _
  unfold UScalar.sub
  by_cases h : y.val ≤ x.val
  · have hb : (⟨BitVec.ofNat _ (x.val - y.val)⟩ : UScalar uty) = ⟨x.bv - y.bv⟩ := by
      apply UScalar.eq_of_val_eq
      have hx := x.hBounds
      show (BitVec.ofNat uty.numBits (x.val - y.val)).toNat = (x.bv - y.bv).toNat
      rw [BitVec.toNat_ofNat, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h),
        Nat.mod_eq_of_lt (by omega)]
      rfl
    rw [ite_eq_right (by omega), ite_eq_left h, wp_ok, hb]
  · rw [ite_eq_left (by omega), ite_eq_right h, wp_fail]

theorem wp_UScalar_mul (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x * y) Q ↔
      if x.val * y.val ≤ UScalar.max uty then Q (.ok ⟨x.bv * y.bv⟩)
      else Q (.error .integerOverflow) := by
  rw [UScalar.mul_def', wp_UScalar_tryMk]
  by_cases h : x.val * y.val < 2 ^ uty.numBits
  · rw [dite_eq_left h, ite_eq_left ((UScalar.lt_pow_iff_le_max _).1 h),
      UScalar.ofNatCore_eq_of_toNat h (b := x.bv * y.bv)
        (by rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h)]
  · rw [dite_eq_right h, ite_eq_right (mt (UScalar.lt_pow_iff_le_max _).2 h)]

theorem wp_UScalar_div (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x / y) Q ↔
      if y.val ≠ 0 then Q (.ok ⟨x.bv / y.bv⟩) else Q (.error .divisionByZero) := by
  change wp (UScalar.div x y) Q ↔ _
  unfold UScalar.div
  have : (y.bv != 0) = true ↔ y.val ≠ 0 := by
    rw [bne_iff_ne, ne_eq, ne_eq, ← BitVec.toNat_inj]
    simp
  by_cases h : y.val ≠ 0
  · rw [ite_eq_left (this.2 h), ite_eq_left h, wp_ok]; rfl
  · rw [ite_eq_right (mt this.1 h), ite_eq_right h, wp_fail]

theorem wp_UScalar_rem (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x % y) Q ↔
      if y.val ≠ 0 then Q (.ok ⟨x.bv % y.bv⟩) else Q (.error .divisionByZero) := by
  change wp (UScalar.rem x y) Q ↔ _
  unfold UScalar.rem
  by_cases h : y.val ≠ 0
  · rw [ite_eq_left (by simpa using h), ite_eq_left h, wp_ok]; rfl
  · rw [ite_eq_right (by simpa using h), ite_eq_right h, wp_fail]

theorem wp_IScalar_add (x y : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (x + y) Q ↔
      if IScalar.min ity ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ity then
        Q (.ok ⟨x.bv + y.bv⟩)
      else Q (.error .integerOverflow) := by
  rw [IScalar.add_def', wp_IScalar_tryMk]
  by_cases h : -2 ^ (ity.numBits - 1) ≤ x.val + y.val ∧ x.val + y.val < 2 ^ (ity.numBits - 1)
  · rw [dite_eq_left h, ite_eq_left ((IScalar.inBounds_iff _).1 h),
      IScalar.ofIntCore_eq_of_toInt h (b := x.bv + y.bv)
        (by rw [BitVec.toInt_add]; exact bmod_pow_numBits_eq_of_lt ity _ h.1 h.2)]
  · rw [dite_eq_right h, ite_eq_right (mt (IScalar.inBounds_iff _).2 h)]

theorem wp_IScalar_sub (x y : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (x - y) Q ↔
      if IScalar.min ity ≤ x.val - y.val ∧ x.val - y.val ≤ IScalar.max ity then
        Q (.ok ⟨x.bv - y.bv⟩)
      else Q (.error .integerOverflow) := by
  rw [IScalar.sub_def', wp_IScalar_tryMk]
  by_cases h : -2 ^ (ity.numBits - 1) ≤ x.val - y.val ∧ x.val - y.val < 2 ^ (ity.numBits - 1)
  · rw [dite_eq_left h, ite_eq_left ((IScalar.inBounds_iff _).1 h),
      IScalar.ofIntCore_eq_of_toInt h (b := x.bv - y.bv)
        (by rw [BitVec.toInt_sub]; exact bmod_pow_numBits_eq_of_lt ity _ h.1 h.2)]
  · rw [dite_eq_right h, ite_eq_right (mt (IScalar.inBounds_iff _).2 h)]

theorem wp_IScalar_mul (x y : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (x * y) Q ↔
      if IScalar.min ity ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ity then
        Q (.ok ⟨x.bv * y.bv⟩)
      else Q (.error .integerOverflow) := by
  rw [IScalar.mul_def', wp_IScalar_tryMk]
  by_cases h : -2 ^ (ity.numBits - 1) ≤ x.val * y.val ∧ x.val * y.val < 2 ^ (ity.numBits - 1)
  · rw [dite_eq_left h, ite_eq_left ((IScalar.inBounds_iff _).1 h),
      IScalar.ofIntCore_eq_of_toInt h (b := x.bv * y.bv)
        (by rw [BitVec.toInt_mul]; exact bmod_pow_numBits_eq_of_lt ity _ h.1 h.2)]
  · rw [dite_eq_right h, ite_eq_right (mt (IScalar.inBounds_iff _).2 h)]

theorem wp_IScalar_neg (x : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (-. x) Q ↔
      if IScalar.min ity ≤ -x.val ∧ -x.val ≤ IScalar.max ity then Q (.ok ⟨-x.bv⟩)
      else Q (.error .integerOverflow) := by
  rw [IScalar.neg_def', wp_IScalar_tryMk]
  by_cases h : -2 ^ (ity.numBits - 1) ≤ -x.val ∧ -x.val < 2 ^ (ity.numBits - 1)
  · rw [dite_eq_left h, ite_eq_left ((IScalar.inBounds_iff _).1 h),
      IScalar.ofIntCore_eq_of_toInt h (b := -x.bv)
        (by rw [BitVec.toInt_neg]; exact bmod_pow_numBits_eq_of_lt ity _ h.1 h.2)]
  · rw [dite_eq_right h, ite_eq_right (mt (IScalar.inBounds_iff _).2 h)]

theorem wp_IScalar_div (x y : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (x / y) Q ↔
      if y.val ≠ 0 then
        (if ¬ (x.val = IScalar.min ity ∧ y.val = -1) then Q (.ok ⟨BitVec.sdiv x.bv y.bv⟩)
         else Q (.error .integerOverflow))
      else Q (.error .divisionByZero) := by
  change wp (IScalar.div x y) Q ↔ _
  unfold IScalar.div
  by_cases h : y.val ≠ 0
  · rw [ite_eq_left (by simpa using h), ite_eq_left h]
    by_cases h' : x.val = IScalar.min ity ∧ y.val = -1
    · rw [ite_eq_right (by simpa using h'), ite_eq_right (by simpa using h'), wp_fail]
    · rw [ite_eq_left (by simpa using h'), ite_eq_left h', wp_ok]
  · rw [ite_eq_right (by simpa using h), ite_eq_right h, wp_fail]

/-- Aeneas' model of `%` on signed integers: `i·::MIN % -1` returns `0` (Rust panics). -/
@[simp] theorem wp_IScalar_rem (x y : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (x % y) Q ↔
      if y.val ≠ 0 then Q (.ok ⟨BitVec.srem x.bv y.bv⟩) else Q (.error .divisionByZero) := by
  change wp (IScalar.rem x y) Q ↔ _
  unfold IScalar.rem
  by_cases h : y.val ≠ 0
  · rw [ite_eq_left (by simpa using h), ite_eq_left h, wp_ok]
  · rw [ite_eq_right (by simpa using h), ite_eq_right h, wp_fail]

/-! ### Bit-vector conditions (for `bv_decide`)

The overflow conditions of `+`, `-`, `*` as bit-vector predicates, so that a symbolically
executed goal is a pure bit-vector problem. -/

theorem wp_UScalar_add_bvc (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x + y) Q ↔
      if x.bv.uaddOverflow y.bv = false then Q (.ok ⟨x.bv + y.bv⟩)
      else Q (.error .integerOverflow) := by
  rw [wp_UScalar_add]
  have : x.bv.uaddOverflow y.bv = false ↔ x.val + y.val ≤ UScalar.max uty := by
    rw [← UScalar.lt_pow_iff_le_max]; simp [BitVec.uaddOverflow]
  by_cases h : x.val + y.val ≤ UScalar.max uty
  · rw [ite_eq_left h, ite_eq_left (this.2 h)]
  · rw [ite_eq_right h, ite_eq_right (mt this.1 h)]

theorem wp_UScalar_sub_bvc (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x - y) Q ↔
      if y.bv ≤ x.bv then Q (.ok ⟨x.bv - y.bv⟩) else Q (.error .integerOverflow) := by
  rw [wp_UScalar_sub]
  have : y.bv ≤ x.bv ↔ y.val ≤ x.val := by rw [BitVec.le_def]; rfl
  by_cases h : y.val ≤ x.val
  · rw [ite_eq_left h, ite_eq_left (this.2 h)]
  · rw [ite_eq_right h, ite_eq_right (mt this.1 h)]

theorem wp_UScalar_mul_bvc (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x * y) Q ↔
      if x.bv.umulOverflow y.bv = false then Q (.ok ⟨x.bv * y.bv⟩)
      else Q (.error .integerOverflow) := by
  rw [wp_UScalar_mul]
  have : x.bv.umulOverflow y.bv = false ↔ x.val * y.val ≤ UScalar.max uty := by
    rw [← UScalar.lt_pow_iff_le_max]; simp [BitVec.umulOverflow]
  by_cases h : x.val * y.val ≤ UScalar.max uty
  · rw [ite_eq_left h, ite_eq_left (this.2 h)]
  · rw [ite_eq_right h, ite_eq_right (mt this.1 h)]

/-! ### Value form (the default `@[simp]` lemmas)

The same operations with the result written as `UScalar.ofNatCore v _` / `IScalar.ofIntCore v _`
where `v` is the mathematical result (the proof argument comes from the branch condition).
Their values simplify with Aeneas' `UScalar.ofNatCore_val_eq` / `IScalar.ofInt_val_eq`, so the
leaves of a proof are linear arithmetic on `.val` (`omega`, `scalar_tac`).  The bit-vector
forms above (`wp_UScalar_add`, …) are the ones to use with `bv_decide`. -/

/-- Signed division truncates toward zero (`Int.tdiv`), as in Rust. -/
theorem IScalar.val_sdiv {x y : IScalar ity} (h0 : y.val ≠ 0)
    (h1 : ¬ (x.val = IScalar.min ity ∧ y.val = -1)) :
    (IScalar.mk (BitVec.sdiv x.bv y.bv)).val = Int.tdiv x.val y.val := by
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.IScalar.div_spec h0 h1
  have : x / y = Result.ok (IScalar.mk (BitVec.sdiv x.bv y.bv)) := by
    change IScalar.div x y = _
    unfold IScalar.div
    rw [ite_eq_left (by simpa using h0), ite_eq_left (by simpa using h1)]
  rw [this] at hz
  cases Result.ok_injective hz
  exact hv

theorem IScalar.tdiv_bounds {x y : IScalar ity} (h0 : y.val ≠ 0)
    (h1 : ¬ (x.val = IScalar.min ity ∧ y.val = -1)) :
    -2 ^ (ity.numBits - 1) ≤ Int.tdiv x.val y.val ∧ Int.tdiv x.val y.val < 2 ^ (ity.numBits - 1) := by
  rw [← IScalar.val_sdiv h0 h1]; exact IScalar.hBounds _

@[simp] theorem wp_UScalar_add_val (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x + y) Q ↔
      if h : x.val + y.val ≤ UScalar.max uty then
        Q (.ok (UScalar.ofNatCore (x.val + y.val) ((UScalar.lt_pow_iff_le_max _).2 h)))
      else Q (.error .integerOverflow) := by
  rw [UScalar.add_def', wp_UScalar_tryMk]
  by_cases h : x.val + y.val ≤ UScalar.max uty
  · rw [dite_eq_left ((UScalar.lt_pow_iff_le_max _).2 h), dite_eq_left h]
  · rw [dite_eq_right (mt (UScalar.lt_pow_iff_le_max _).1 h), dite_eq_right h]

@[simp] theorem wp_UScalar_sub_val (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x - y) Q ↔
      if y.val ≤ x.val then
        Q (.ok (UScalar.ofNatCore (x.val - y.val) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.hBounds)))
      else Q (.error .integerOverflow) := by
  rw [wp_UScalar_sub]
  by_cases h : y.val ≤ x.val
  · have hb : (x.bv - y.bv).toNat = x.val - y.val := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h)]; rfl
    rw [ite_eq_left h, ite_eq_left h, UScalar.ofNatCore_eq_of_toNat _ hb]
  · rw [ite_eq_right h, ite_eq_right h]

@[simp] theorem wp_UScalar_mul_val (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x * y) Q ↔
      if h : x.val * y.val ≤ UScalar.max uty then
        Q (.ok (UScalar.ofNatCore (x.val * y.val) ((UScalar.lt_pow_iff_le_max _).2 h)))
      else Q (.error .integerOverflow) := by
  rw [UScalar.mul_def', wp_UScalar_tryMk]
  by_cases h : x.val * y.val ≤ UScalar.max uty
  · rw [dite_eq_left ((UScalar.lt_pow_iff_le_max _).2 h), dite_eq_left h]
  · rw [dite_eq_right (mt (UScalar.lt_pow_iff_le_max _).1 h), dite_eq_right h]

@[simp] theorem wp_UScalar_div_val (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x / y) Q ↔
      if y.val ≠ 0 then
        Q (.ok (UScalar.ofNatCore (x.val / y.val)
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.hBounds)))
      else Q (.error .divisionByZero) := by
  rw [wp_UScalar_div]
  by_cases h : y.val ≠ 0
  · have hb : (x.bv / y.bv).toNat = x.val / y.val := by rw [BitVec.toNat_udiv]; rfl
    rw [ite_eq_left h, ite_eq_left h, UScalar.ofNatCore_eq_of_toNat _ hb]
  · rw [ite_eq_right h, ite_eq_right h]

@[simp] theorem wp_UScalar_rem_val (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x % y) Q ↔
      if y.val ≠ 0 then
        Q (.ok (UScalar.ofNatCore (x.val % y.val)
          (Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.hBounds)))
      else Q (.error .divisionByZero) := by
  rw [wp_UScalar_rem]
  by_cases h : y.val ≠ 0
  · have hb : (x.bv % y.bv).toNat = x.val % y.val := by rw [BitVec.toNat_umod]; rfl
    rw [ite_eq_left h, ite_eq_left h, UScalar.ofNatCore_eq_of_toNat _ hb]
  · rw [ite_eq_right h, ite_eq_right h]

@[simp] theorem wp_IScalar_add_val (x y : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (x + y) Q ↔
      if h : IScalar.min ity ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ity then
        Q (.ok (IScalar.ofIntCore (x.val + y.val) ((IScalar.inBounds_iff _).2 h)))
      else Q (.error .integerOverflow) := by
  rw [IScalar.add_def', wp_IScalar_tryMk]
  by_cases h : IScalar.min ity ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ity
  · rw [dite_eq_left ((IScalar.inBounds_iff _).2 h), dite_eq_left h]
  · rw [dite_eq_right (mt (IScalar.inBounds_iff _).1 h), dite_eq_right h]

@[simp] theorem wp_IScalar_sub_val (x y : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (x - y) Q ↔
      if h : IScalar.min ity ≤ x.val - y.val ∧ x.val - y.val ≤ IScalar.max ity then
        Q (.ok (IScalar.ofIntCore (x.val - y.val) ((IScalar.inBounds_iff _).2 h)))
      else Q (.error .integerOverflow) := by
  rw [IScalar.sub_def', wp_IScalar_tryMk]
  by_cases h : IScalar.min ity ≤ x.val - y.val ∧ x.val - y.val ≤ IScalar.max ity
  · rw [dite_eq_left ((IScalar.inBounds_iff _).2 h), dite_eq_left h]
  · rw [dite_eq_right (mt (IScalar.inBounds_iff _).1 h), dite_eq_right h]

@[simp] theorem wp_IScalar_mul_val (x y : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (x * y) Q ↔
      if h : IScalar.min ity ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ity then
        Q (.ok (IScalar.ofIntCore (x.val * y.val) ((IScalar.inBounds_iff _).2 h)))
      else Q (.error .integerOverflow) := by
  rw [IScalar.mul_def', wp_IScalar_tryMk]
  by_cases h : IScalar.min ity ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ity
  · rw [dite_eq_left ((IScalar.inBounds_iff _).2 h), dite_eq_left h]
  · rw [dite_eq_right (mt (IScalar.inBounds_iff _).1 h), dite_eq_right h]

@[simp] theorem wp_IScalar_neg_val (x : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (-. x) Q ↔
      if h : IScalar.min ity ≤ -x.val ∧ -x.val ≤ IScalar.max ity then
        Q (.ok (IScalar.ofIntCore (-x.val) ((IScalar.inBounds_iff _).2 h)))
      else Q (.error .integerOverflow) := by
  rw [IScalar.neg_def', wp_IScalar_tryMk]
  by_cases h : IScalar.min ity ≤ -x.val ∧ -x.val ≤ IScalar.max ity
  · rw [dite_eq_left ((IScalar.inBounds_iff _).2 h), dite_eq_left h]
  · rw [dite_eq_right (mt (IScalar.inBounds_iff _).1 h), dite_eq_right h]

@[simp] theorem wp_IScalar_div_val (x y : IScalar ity) (Q : Except Error (IScalar ity) → Prop) :
    wp (x / y) Q ↔
      if h0 : y.val ≠ 0 then
        (if h1 : ¬ (x.val = IScalar.min ity ∧ y.val = -1) then
          Q (.ok (IScalar.ofIntCore (Int.tdiv x.val y.val) (IScalar.tdiv_bounds h0 h1)))
         else Q (.error .integerOverflow))
      else Q (.error .divisionByZero) := by
  rw [wp_IScalar_div]
  by_cases h0 : y.val ≠ 0
  · rw [ite_eq_left h0, dite_eq_left h0]
    by_cases h1 : ¬ (x.val = IScalar.min ity ∧ y.val = -1)
    · rw [ite_eq_left h1, dite_eq_left h1,
        IScalar.ofIntCore_eq_of_toInt _ (b := BitVec.sdiv x.bv y.bv) (IScalar.val_sdiv h0 h1)]
    · rw [ite_eq_right h1, dite_eq_right h1]
  · rw [ite_eq_right h0, dite_eq_right h0]

/-! Shifts by an unsigned amount (`x << s`, `x >> s`): they panic when `s` is not below the
bit width. -/

@[simp] theorem wp_UScalar_shl {ty' : UScalarTy} (x : UScalar uty) (s : UScalar ty')
    (Q : Except Error (UScalar uty) → Prop) :
    wp (x <<< s) Q ↔
      if s.val < uty.numBits then Q (.ok ⟨x.bv <<< s.val⟩) else Q (.error .integerOverflow) := by
  change wp (UScalar.shiftLeft x s.val) Q ↔ _
  unfold UScalar.shiftLeft
  by_cases h : s.val < uty.numBits
  · rw [ite_eq_left h, ite_eq_left h, wp_ok]; rfl
  · rw [ite_eq_right h, ite_eq_right h, wp_fail]

@[simp] theorem wp_UScalar_shr {ty' : UScalarTy} (x : UScalar uty) (s : UScalar ty')
    (Q : Except Error (UScalar uty) → Prop) :
    wp (x >>> s) Q ↔
      if s.val < uty.numBits then Q (.ok ⟨x.bv >>> s.val⟩) else Q (.error .integerOverflow) := by
  change wp (UScalar.shiftRight x s.val) Q ↔ _
  unfold UScalar.shiftRight
  by_cases h : s.val < uty.numBits
  · rw [ite_eq_left h, ite_eq_left h, wp_ok]; rfl
  · rw [ite_eq_right h, ite_eq_right h, wp_fail]

end scalar

end EquivLean.Aeneas
