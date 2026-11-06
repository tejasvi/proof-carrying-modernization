import EquivLean.Bridge.Aeneas.Behaves

/-!
# Aeneas (Rust) bridge: values and their mathematical models

* `Corr` instances: unsigned scalars ↔ `Nat` (value) and `BitVec` (representation), signed
  scalars ↔ `Int` and `BitVec`, `Slice α`, `alloc.vec.Vec α`, `Array α n` ↔ `List α`, and
  Rust outcomes ↔ outcomes (same panic reason, corresponding values).
* Leaf lemmas for the values produced by the bit-vector forms of the scalar `wp` lemmas of
  `Behaves.lean`: the result of `x + y` there is `⟨x.bv + y.bv⟩`, whose value is
  `x.val + y.val` in the non-overflow branch (`UScalar.val_add_of_le`, a conditional `@[simp]`
  lemma) and `(x.val + y.val) % 2 ^ n` in general (`UScalar.val_add`); the same for `-`, `*`,
  `/`, `%`, shifts, and the signed operations.  (The default value-form lemmas need none of
  this: `(UScalar.ofNatCore v _).val = v` is Aeneas' `UScalar.ofNatCore_val_eq`.)
* Casts and library functions: `UScalar.hcast_val_of_numBits_lt` (widening `u16 as i128`),
  `UScalar.val_saturating_add`, `core.num.U32.saturating_add_eq`, ….
-/

open Aeneas Aeneas.Std

namespace EquivLean.Aeneas

universe u

/-! ## Correspondences -/

instance instCorrUScalarNat {ty : UScalarTy} : Corr (UScalar ty) Nat := ⟨fun a n => a.val = n⟩
instance instCorrIScalarInt {ty : IScalarTy} : Corr (IScalar ty) Int := ⟨fun a n => a.val = n⟩
instance instCorrUScalarBitVec {ty : UScalarTy} : Corr (UScalar ty) (BitVec ty.numBits) :=
  ⟨fun a b => a.bv = b⟩
instance instCorrIScalarBitVec {ty : IScalarTy} : Corr (IScalar ty) (BitVec ty.numBits) :=
  ⟨fun a b => a.bv = b⟩
instance instCorrSliceList {α : Type u} : Corr (Slice α) (List α) := ⟨fun s l => s.val = l⟩
instance instCorrVecList {α : Type u} : Corr (alloc.vec.Vec α) (List α) := ⟨fun v l => v.val = l⟩
instance instCorrArrayList {α : Type u} {n : Usize} : Corr (Std.Array α n) (List α) :=
  ⟨fun a l => a.val = l⟩

/-- Rust outcomes correspond when both return corresponding values, or both panic with the
same reason. -/
def outcomeRel {α β : Type u} (r : α → β → Prop) : Except Error α → Except Error β → Prop
  | .ok a, .ok b => r a b
  | .error e, .error e' => e = e'
  | _, _ => False

instance instCorrOutcome {α β : Type u} [Corr α β] : Corr (Except Error α) (Except Error β) :=
  ⟨outcomeRel Corr.corr⟩

@[simp] theorem outcomeRel_ok_ok {α β : Type u} (r : α → β → Prop) (a : α) (b : β) :
    outcomeRel r (.ok a) (.ok b) ↔ r a b := Iff.rfl
@[simp] theorem outcomeRel_error_error {α β : Type u} (r : α → β → Prop) (e e' : Error) :
    outcomeRel r (.error e : Except Error α) (.error e' : Except Error β) ↔ e = e' := Iff.rfl
@[simp] theorem outcomeRel_ok_error {α β : Type u} (r : α → β → Prop) (a : α) (e : Error) :
    outcomeRel r (.ok a) (.error e : Except Error β) ↔ False := Iff.rfl
@[simp] theorem outcomeRel_error_ok {α β : Type u} (r : α → β → Prop) (e : Error) (b : β) :
    outcomeRel r (.error e : Except Error α) (.ok b) ↔ False := Iff.rfl

theorem outcomeRel_eq {α : Type u} (o o' : Except Error α) : outcomeRel (· = ·) o o' ↔ o = o' := by
  cases o <;> cases o' <;> simp [outcomeRel]

@[simp] theorem corr_uscalar_nat {ty : UScalarTy} (a : UScalar ty) (n : Nat) :
    Corr.corr a n ↔ a.val = n := Iff.rfl
@[simp] theorem corr_iscalar_int {ty : IScalarTy} (a : IScalar ty) (n : Int) :
    Corr.corr a n ↔ a.val = n := Iff.rfl
@[simp] theorem corr_slice_list {α : Type u} (s : Slice α) (l : List α) :
    Corr.corr s l ↔ s.val = l := Iff.rfl
@[simp] theorem corr_vec_list {α : Type u} (v : alloc.vec.Vec α) (l : List α) :
    Corr.corr v l ↔ v.val = l := Iff.rfl

/-! ## Unsigned scalars -/

namespace UScalar
variable {ty : UScalarTy}

theorem val_mk (b : BitVec ty.numBits) : (UScalar.mk b : UScalar ty).val = b.toNat := rfl

theorem val_lt (x : UScalar ty) : x.val < 2 ^ ty.numBits := x.hBounds

theorem val_le_max (x : UScalar ty) : x.val ≤ UScalar.max ty :=
  (lt_pow_iff_le_max _).1 x.hBounds

@[simp high] theorem val_add_of_le {x y : UScalar ty} (h : x.val + y.val ≤ UScalar.max ty) :
    (UScalar.mk (x.bv + y.bv)).val = x.val + y.val := by
  rw [val_mk, BitVec.toNat_add]; exact Nat.mod_eq_of_lt ((lt_pow_iff_le_max _).2 h)

@[simp] theorem val_add (x y : UScalar ty) :
    (UScalar.mk (x.bv + y.bv)).val = (x.val + y.val) % 2 ^ ty.numBits := by
  rw [val_mk, BitVec.toNat_add]; rfl

@[simp high] theorem val_sub_of_le {x y : UScalar ty} (h : y.val ≤ x.val) :
    (UScalar.mk (x.bv - y.bv)).val = x.val - y.val := by
  rw [val_mk, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h)]; rfl

@[simp high] theorem val_mul_of_le {x y : UScalar ty} (h : x.val * y.val ≤ UScalar.max ty) :
    (UScalar.mk (x.bv * y.bv)).val = x.val * y.val := by
  rw [val_mk, BitVec.toNat_mul]; exact Nat.mod_eq_of_lt ((lt_pow_iff_le_max _).2 h)

@[simp] theorem val_mul (x y : UScalar ty) :
    (UScalar.mk (x.bv * y.bv)).val = (x.val * y.val) % 2 ^ ty.numBits := by
  rw [val_mk, BitVec.toNat_mul]; rfl

@[simp] theorem val_div (x y : UScalar ty) :
    (UScalar.mk (x.bv / y.bv)).val = x.val / y.val := by
  rw [val_mk, BitVec.toNat_udiv]; rfl

@[simp] theorem val_rem (x y : UScalar ty) :
    (UScalar.mk (x.bv % y.bv)).val = x.val % y.val := by
  rw [val_mk, BitVec.toNat_umod]; rfl

@[simp] theorem val_shl (x : UScalar ty) (s : Nat) :
    (UScalar.mk (x.bv <<< s)).val = (x.val <<< s) % 2 ^ ty.numBits := by
  rw [val_mk, BitVec.toNat_shiftLeft]; rfl

@[simp] theorem val_shr (x : UScalar ty) (s : Nat) :
    (UScalar.mk (x.bv >>> s)).val = x.val >>> s := by
  rw [val_mk, BitVec.toNat_ushiftRight]; rfl

@[simp] theorem val_saturating_add (x y : UScalar ty) :
    (UScalar.saturating_add x y).val = min (UScalar.max ty) (x.val + y.val) := by
  rw [UScalar.saturating_add, val_mk, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := (lt_pow_iff_le_max (uty := ty) (UScalar.max ty)).2 (Nat.le_refl _)
  omega

/-- Widening unsigned → signed cast (`days as i128`) keeps the value. -/
@[simp] theorem hcast_val_of_numBits_lt {tgt : IScalarTy} (x : UScalar ty)
    (h : ty.numBits < tgt.numBits) : (UScalar.hcast tgt x).val = x.val := by
  rw [UScalar.hcast_val_eq]
  have hx := x.hBounds
  have h2 : (2:Nat) ^ ty.numBits ≤ 2 ^ (tgt.numBits - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' _ _ (IScalarTy.numBits_nonzero tgt)
  · have : (0:Int) ≤ 2 ^ (tgt.numBits - 1) := by positivity
    omega
  · exact_mod_cast Nat.lt_of_lt_of_le hx h2

/-- Equality of unsigned scalars is equality of values (`omega`-friendly). -/
theorem eq_iff_val (x y : UScalar ty) : x = y ↔ x.val = y.val := UScalar.eq_equiv x y

theorem mk_eq_iff (b : BitVec ty.numBits) (y : UScalar ty) : UScalar.mk b = y ↔ b = y.bv := by
  cases y; simp

end UScalar

/-! ## Signed scalars -/

namespace IScalar
variable {ty : IScalarTy}

theorem val_mk (b : BitVec ty.numBits) : (IScalar.mk b : IScalar ty).val = b.toInt := rfl

@[simp high] theorem val_add_of_bounds {x y : IScalar ty}
    (h : IScalar.min ty ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ty) :
    (IScalar.mk (x.bv + y.bv)).val = x.val + y.val := by
  have h' := (inBounds_iff _).2 h
  rw [val_mk, BitVec.toInt_add]; exact bmod_pow_numBits_eq_of_lt ty _ h'.1 h'.2

@[simp high] theorem val_sub_of_bounds {x y : IScalar ty}
    (h : IScalar.min ty ≤ x.val - y.val ∧ x.val - y.val ≤ IScalar.max ty) :
    (IScalar.mk (x.bv - y.bv)).val = x.val - y.val := by
  have h' := (inBounds_iff _).2 h
  rw [val_mk, BitVec.toInt_sub]; exact bmod_pow_numBits_eq_of_lt ty _ h'.1 h'.2

@[simp high] theorem val_mul_of_bounds {x y : IScalar ty}
    (h : IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty) :
    (IScalar.mk (x.bv * y.bv)).val = x.val * y.val := by
  have h' := (inBounds_iff _).2 h
  rw [val_mk, BitVec.toInt_mul]; exact bmod_pow_numBits_eq_of_lt ty _ h'.1 h'.2

@[simp high] theorem val_neg_of_bounds {x : IScalar ty}
    (h : IScalar.min ty ≤ -x.val ∧ -x.val ≤ IScalar.max ty) :
    (IScalar.mk (-x.bv)).val = -x.val := by
  have h' := (inBounds_iff _).2 h
  rw [val_mk, BitVec.toInt_neg]; exact bmod_pow_numBits_eq_of_lt ty _ h'.1 h'.2

theorem eq_iff_val (x y : IScalar ty) : x = y ↔ x.val = y.val := IScalar.eq_equiv x y

end IScalar

@[simp] theorem core.num.U8.saturating_add_eq (x y : U8) :
    core.num.U8.saturating_add x y = UScalar.saturating_add x y := rfl
@[simp] theorem core.num.U16.saturating_add_eq (x y : U16) :
    core.num.U16.saturating_add x y = UScalar.saturating_add x y := rfl
@[simp] theorem core.num.U32.saturating_add_eq (x y : U32) :
    core.num.U32.saturating_add x y = UScalar.saturating_add x y := rfl
@[simp] theorem core.num.U64.saturating_add_eq (x y : U64) :
    core.num.U64.saturating_add x y = UScalar.saturating_add x y := rfl
@[simp] theorem core.num.Usize.saturating_add_eq (x y : Usize) :
    core.num.Usize.saturating_add x y = UScalar.saturating_add x y := rfl

/-! ## Collections -/

@[simp] theorem Slice.len_val' {α : Type u} (v : Slice α) : (Slice.len v).val = v.val.length :=
  Slice.len_val v

theorem Slice.length_le_max {α : Type u} (v : Slice α) : v.val.length ≤ Usize.max :=
  v.property

end EquivLean.Aeneas
