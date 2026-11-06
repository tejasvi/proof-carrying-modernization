import EquivLean.Repr.Corr

/-!
# Machine integers across encodings

The five encodings represent a `w`-bit integer in three ways:

| encoding | signed `int32_t`/`int`/`i32` | unsigned |
|---|---|---|
| cirlean | `Val.int (v : Int)` with a range check, signed overflow undefined | `Val.int` wrapped |
| JimpleLean | `Value.int (BitVec 32)`, wrapping | `char` as `BitVec 32` |
| Aeneas | `I32 = IScalar .I32` (`bv : BitVec 32`), checked: overflow panics | `U32` (`bv`) |
| StrictTS | `number` (F64) with the `| 0` / `Math.imul` int32 idioms | `>>> 0` |
| coblean | `PIC S9(n) COMP-5` bytes, decoded to `Int` | `PIC 9(n) COMP-5` |

The common model is the mathematical integer `Int` (or `Nat`) together with its range, and
`BitVec w` for bit-level reasoning.  `SRepr w b v` / `URepr w b v` relate a bit vector to the
integer it stands for; the lemmas below move arithmetic, comparisons and wrapping between the
two views, so that a leaf goal mixing `BitVec` from one encoding and `Int` from another can
be normalized to `omega` (linear integer arithmetic) or to `bv_decide` (bit blasting).
-/

namespace EquivLean

/-- `x` fits a signed `w`-bit integer. -/
def SRange (w : Nat) (x : Int) : Prop := -2 ^ (w - 1) ≤ x ∧ x < 2 ^ (w - 1)

/-- `x` fits an unsigned `w`-bit integer. -/
def URange (w : Nat) (x : Int) : Prop := 0 ≤ x ∧ x < 2 ^ w

instance (w : Nat) (x : Int) : Decidable (SRange w x) := inferInstanceAs (Decidable (_ ∧ _))
instance (w : Nat) (x : Int) : Decidable (URange w x) := inferInstanceAs (Decidable (_ ∧ _))

/-- Two's-complement wrap of an integer into `w` bits (what Java's `int` arithmetic,
`Math.imul`, Rust's `wrapping_*` and C's unsigned arithmetic do). -/
def wrapS (w : Nat) (x : Int) : Int := x.bmod (2 ^ w)

/-- Unsigned wrap. -/
def wrapU (w : Nat) (x : Int) : Int := x % (2 ^ w : Nat)

/-- The bit vector `b` stands for the signed integer `v`. -/
def SRepr {w : Nat} (b : BitVec w) (v : Int) : Prop := b.toInt = v

/-- The bit vector `b` stands for the unsigned integer `v`. -/
def URepr {w : Nat} (b : BitVec w) (v : Nat) : Prop := b.toNat = v

theorem toInt_srange {w : Nat} (b : BitVec w) : SRange w b.toInt :=
  ⟨BitVec.le_toInt b, BitVec.toInt_lt⟩

theorem toNat_urange {w : Nat} (b : BitVec w) : URange w b.toNat := by
  refine ⟨by omega, ?_⟩
  have := b.isLt
  exact_mod_cast this

@[simp] theorem toInt_ofInt_eq_wrapS (w : Nat) (x : Int) : (BitVec.ofInt w x).toInt = wrapS w x :=
  BitVec.toInt_ofInt x

theorem wrapS_of_srange {w : Nat} (hw : 0 < w) {x : Int} (h : SRange w x) : wrapS w x = x := by
  rw [← toInt_ofInt_eq_wrapS]
  exact BitVec.toInt_ofInt_eq_self hw h.1 h.2

theorem toInt_ofInt_of_srange {w : Nat} (hw : 0 < w) {x : Int} (h : SRange w x) :
    (BitVec.ofInt w x).toInt = x :=
  BitVec.toInt_ofInt_eq_self hw h.1 h.2

/-- Signed addition without overflow is mathematical addition. -/
theorem toInt_add_of_srange {w : Nat} {x y : BitVec w} (h : SRange w (x.toInt + y.toInt)) :
    (x + y).toInt = x.toInt + y.toInt := by
  apply BitVec.toInt_add_of_not_saddOverflow
  simp only [BitVec.saddOverflow, decide_eq_true_eq, Bool.or_eq_true]
  unfold SRange at h
  omega

/-- Signed subtraction without overflow is mathematical subtraction. -/
theorem toInt_sub_of_srange {w : Nat} {x y : BitVec w} (h : SRange w (x.toInt - y.toInt)) :
    (x - y).toInt = x.toInt - y.toInt := by
  apply BitVec.toInt_sub_of_not_ssubOverflow
  simp only [BitVec.ssubOverflow, decide_eq_true_eq, Bool.or_eq_true]
  unfold SRange at h
  omega

/-- Signed multiplication without overflow is mathematical multiplication. -/
theorem toInt_mul_of_srange {w : Nat} {x y : BitVec w} (h : SRange w (x.toInt * y.toInt)) :
    (x * y).toInt = x.toInt * y.toInt := by
  apply BitVec.toInt_mul_of_not_smulOverflow
  simp only [BitVec.smulOverflow, decide_eq_true_eq, Bool.or_eq_true]
  unfold SRange at h
  omega

/-- Wrapping signed addition (Java `int`, Rust `wrapping_add`, `Math.imul`-style idioms). -/
theorem toInt_add_wrap {w : Nat} (x y : BitVec w) :
    (x + y).toInt = wrapS w (x.toInt + y.toInt) := by
  rw [← toInt_ofInt_eq_wrapS, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

theorem toInt_mul_wrap {w : Nat} (x y : BitVec w) :
    (x * y).toInt = wrapS w (x.toInt * y.toInt) := by
  rw [← toInt_ofInt_eq_wrapS, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

/-- Unsigned addition without overflow is mathematical addition. -/
theorem toNat_add_of_lt {w : Nat} {x y : BitVec w} (h : x.toNat + y.toNat < 2 ^ w) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_mul_of_lt {w : Nat} {x y : BitVec w} (h : x.toNat * y.toNat < 2 ^ w) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_sub_of_le {w : Nat} {x y : BitVec w} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using h)]

/-- Comparisons agree between the views. -/
theorem slt_iff {w : Nat} (x y : BitVec w) : x.slt y = true ↔ x.toInt < y.toInt :=
  BitVec.slt_iff_toInt_lt

theorem ult_iff {w : Nat} (x y : BitVec w) : x.ult y = true ↔ x.toNat < y.toNat :=
  BitVec.ult_iff_toNat_lt

theorem eq_iff_toInt {w : Nat} (x y : BitVec w) : x = y ↔ x.toInt = y.toInt :=
  ⟨fun h => h ▸ rfl, BitVec.eq_of_toInt_eq⟩

theorem eq_iff_toNat {w : Nat} (x y : BitVec w) : x = y ↔ x.toNat = y.toNat :=
  ⟨fun h => h ▸ rfl, BitVec.eq_of_toNat_eq⟩

/-- Signed and unsigned readings of the same bits. -/
theorem toInt_eq_ite {w : Nat} (x : BitVec w) :
    x.toInt = if 2 * x.toNat < 2 ^ w then (x.toNat : Int) else (x.toNat : Int) - 2 ^ w :=
  BitVec.toInt_eq_toNat_cond x

end EquivLean
