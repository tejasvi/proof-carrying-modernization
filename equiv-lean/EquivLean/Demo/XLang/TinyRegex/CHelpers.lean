import CIR
import EquivLean.Demo.Gen.Cir.TinyRegex
import EquivLean.Demo.XLang.TinyRegex.Model
import EquivLean.Demo.XLang.TinyRegex.CBase

/-!
# tiny-regex-c → model, C side: the character helpers

Contracts (`Returns`, total correctness) of the leaf functions of `re.c` that test one character:
`matchdigit`, `matchalpha`, `matchwhitespace` (glibc's `__ctype_b_loc` table, indexed from -128: a
negative `char` is in no class), `matchalphanum`, `matchdot`, `ismetachar`, on a `char` value `c`
(`-128 ≤ c ≤ 127`); each result is non-zero exactly when the C test holds.  None of them has
undefined behaviour.  The `_iff` lemmas give the model's tests on the byte `b` of `c = sc b`.
-/

open CIR CIR.Std EquivLean.Demo.Gen.Cir.TinyRegex

set_option maxHeartbeats 4000000

namespace EquivLean.Demo.XLang.TinyRegex.C

open EquivLean.Demo.XLang.TinyRegex (sc isdigitC isalphaC isspaceC matchalphanum ismetachar)

theorem sc_range {b : Nat} (h : b < 256) : -128 ≤ sc b ∧ sc b ≤ 127 := by
  unfold sc; split <;> omega

theorem isdigitC_iff {b : Nat} (h : b < 256) : isdigitC b = true ↔ 48 ≤ sc b ∧ sc b ≤ 57 := by
  unfold isdigitC sc; split <;> simp <;> omega

theorem isalphaC_iff {b : Nat} (h : b < 256) :
    isalphaC b = true ↔ (65 ≤ sc b ∧ sc b ≤ 90) ∨ (97 ≤ sc b ∧ sc b ≤ 122) := by
  unfold isalphaC sc; split <;> simp <;> omega

theorem isspaceC_iff {b : Nat} (h : b < 256) : isspaceC b = true ↔ sc b = 32 ∨ (9 ≤ sc b ∧ sc b ≤ 13) := by
  unfold isspaceC sc; split <;> simp <;> omega

theorem matchalphanum_iff {b : Nat} (h : b < 256) :
    matchalphanum b = true ↔
      sc b = 95 ∨ (65 ≤ sc b ∧ sc b ≤ 90) ∨ (97 ≤ sc b ∧ sc b ≤ 122) ∨ (48 ≤ sc b ∧ sc b ≤ 57) := by
  unfold matchalphanum isalphaC isdigitC sc; split <;> simp <;> omega

theorem ismetachar_iff {b : Nat} (h : b < 256) :
    ismetachar b = true ↔ (sc b = 115 ∨ sc b = 83 ∨ sc b = 119 ∨ sc b = 87 ∨ sc b = 100 ∨ sc b = 68) := by
  unfold ismetachar sc; split <;> simp <;> omega

/-- A signed 32-bit bitwise result is an `int`. -/
theorem bitwise_s32_range (f : BitVec 32 → BitVec 32 → BitVec 32) (x y : Int) :
    -2147483648 ≤ bitwise true 32 f x y ∧ bitwise true 32 f x y ≤ 2147483647 := by
  unfold bitwise
  have h1 := BitVec.le_toInt (f (BitVec.ofInt 32 x) (BitVec.ofInt 32 y))
  have h2 := (BitVec.toInt_lt (x := f (BitVec.ofInt 32 x) (BitVec.ofInt 32 y)))
  simp only [ite_true]
  constructor <;> simp at h1 h2 <;> omega

/-- `matchdigit(c)`: `isdigit(c)`. -/
@[cir_spec]
theorem matchdigit_spec (c : Int) (hc : -128 ≤ c ∧ c ≤ 127) (m : Mem) :
    Returns ctx fn_matchdigit.sym [.int c] m
      (fun r m' => (∃ v, r = some (.int v) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧ (v ≠ 0 ↔ 48 ≤ c ∧ c ≤ 57)) ∧ Frame m m' []) := by
  have hr := ctypeEntry_range c (by omega) (by omega)
  have hd := ctype_digit c (by omega) (by omega)
  have cirH_bw : ∀ e : Int, -2147483648 ≤ bitwise true 32 (fun x1 x2 => x1 &&& x2) e 2048 ∧
      bitwise true 32 (fun x1 x2 => x1 &&& x2) e 2048 ≤ 2147483647 := fun e => bitwise_s32_range _ e 2048
  unfold ctypeHas at hd
  cir_start
  cir_vcg

/-- `matchalpha(c)`: `isalpha(c)`. -/
@[cir_spec]
theorem matchalpha_spec (c : Int) (hc : -128 ≤ c ∧ c ≤ 127) (m : Mem) :
    Returns ctx fn_matchalpha.sym [.int c] m
      (fun r m' => (∃ v, r = some (.int v) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧ (v ≠ 0 ↔ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122))) ∧
        Frame m m' []) := by
  have hr := ctypeEntry_range c (by omega) (by omega)
  have hd := ctype_alpha c (by omega) (by omega)
  have cirH_bw : ∀ e : Int, -2147483648 ≤ bitwise true 32 (fun x1 x2 => x1 &&& x2) e 1024 ∧
      bitwise true 32 (fun x1 x2 => x1 &&& x2) e 1024 ≤ 2147483647 := fun e => bitwise_s32_range _ e 1024
  unfold ctypeHas at hd
  cir_start
  cir_vcg

/-- `matchwhitespace(c)`: `isspace(c)`. -/
@[cir_spec]
theorem matchwhitespace_spec (c : Int) (hc : -128 ≤ c ∧ c ≤ 127) (m : Mem) :
    Returns ctx fn_matchwhitespace.sym [.int c] m
      (fun r m' => (∃ v, r = some (.int v) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧ (v ≠ 0 ↔ c = 32 ∨ (9 ≤ c ∧ c ≤ 13))) ∧ Frame m m' []) := by
  have hr := ctypeEntry_range c (by omega) (by omega)
  have hd := ctype_space c (by omega) (by omega)
  have cirH_bw : ∀ e : Int, -2147483648 ≤ bitwise true 32 (fun x1 x2 => x1 &&& x2) e 8192 ∧
      bitwise true 32 (fun x1 x2 => x1 &&& x2) e 8192 ≤ 2147483647 := fun e => bitwise_s32_range _ e 8192
  unfold ctypeHas at hd
  cir_start
  cir_vcg

/-- `matchdot(c)`: 1 (`RE_DOT_MATCHES_NEWLINE` is 1). -/
@[cir_spec]
theorem matchdot_spec (c : Int) (hc : -128 ≤ c ∧ c ≤ 127) (m : Mem) :
    Returns ctx fn_matchdot.sym [.int c] m (fun r m' => r = some (.int 1) ∧ Frame m m' []) := by
  cir_start
  cir_vcg

/-- `ismetachar(c)`. -/
@[cir_spec]
theorem ismetachar_spec (c : Int) (hc : -128 ≤ c ∧ c ≤ 127) (m : Mem) :
    Returns ctx fn_ismetachar.sym [.int c] m
      (fun r m' => (∃ v, r = some (.int v) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧
        (v ≠ 0 ↔ metacharP c)) ∧ Frame m m' []) := by
  unfold metacharP
  cir_start
  cir_vcg

set_option cir.inline false in
/-- `matchalphanum(c)`: `(c == '_') || matchalpha(c) || matchdigit(c)`. -/
@[cir_spec]
theorem matchalphanum_spec (c : Int) (hc : -128 ≤ c ∧ c ≤ 127) (m : Mem) :
    Returns ctx fn_matchalphanum.sym [.int c] m
      (fun r m' => (∃ v, r = some (.int v) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧
        (v ≠ 0 ↔ c = 95 ∨ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (48 ≤ c ∧ c ≤ 57))) ∧
        Frame m m' []) := by
  have cirH_c := hc
  cir_start
  cir_vcg

end EquivLean.Demo.XLang.TinyRegex.C
