import EquivLean.Demo.XLang.Adler32.CCombine
import EquivLean.Demo.XLang.Adler32.Equiv
import EquivLean.Demo.XLang.Adler32.RustDefs

/-!
# zlib adler32 → model, C side: `adler32_combine`, `adler32_combine64` and their runs

* `adler32_combine_spec`, `adler32_combine64_spec` (`Returns`, every input): both call `adler32_combine_` (its
  `@[cir_spec]` contract) and return its value, the model's `combine adler1 adler2 len2`.
* `cRunCb x`, `cRunCb64 x`: the call `adler32_combine(adler1, adler2, len2)` (`adler32_combine64`) from the module's
  initial memory, on the Rust side's input `x : CbInput`.
* `ctotal_cb`, `ctotal_cb64`: `CTotal cbLong cbModel cRunCb` (`cRunCb64`): every run returns the model's value.
-/

open CIR EquivLean.Cir Aeneas.Std
open EquivLean.Demo.Gen.Cir.Adler32.Adler32 (ctx module)
open EquivLean.Demo.XLang.Adler32 (combine CbInput cbLong cbModel CTotal)

set_option maxHeartbeats 4000000

namespace EquivLean.Demo.XLang.Adler32.C

/-- The model's `combine` is an `unsigned long` (it is stored in the caller's return slot). -/
theorem combine_lt (a1 a2 : Nat) (len2 : Int) : combine a1 a2 len2 < 18446744073709551616 := by
  by_cases h : len2 < 0
  · rw [combine_neg a1 a2 len2 h]; decide
  · rw [combine_nonneg a1 a2 len2 h]
    refine Nat.lt_of_lt_of_le (Nat.or_lt_two_pow (n := 64) ?_ ?_) (by decide)
    · (repeat' split) <;> omega
    · (repeat' split) <;> omega

set_option cir.inline false in
/-- `adler32_combine(adler1, adler2, len2)`: `adler32_combine_(adler1, adler2, len2)`. -/
@[cir_spec]
theorem adler32_combine_spec (a1 a2 : Nat) (len2 : Int) (m : Mem) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64)
    (hl : -9223372036854775808 ≤ len2 ∧ len2 ≤ 9223372036854775807) :
    Returns ctx "adler32_combine" [.int a1, .int a2, .int len2] m
      (fun r m' => r = some (.int (combine a1 a2 len2)) ∧ m.next ≤ m'.next ∧
        ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_cb := combine_lt a1 a2 len2
  cir_start
  cir_vcg

set_option cir.inline false in
/-- `adler32_combine64(adler1, adler2, len2)`: `adler32_combine_(adler1, adler2, len2)`. -/
@[cir_spec]
theorem adler32_combine64_spec (a1 a2 : Nat) (len2 : Int) (m : Mem) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64)
    (hl : -9223372036854775808 ≤ len2 ∧ len2 ≤ 9223372036854775807) :
    Returns ctx "adler32_combine64" [.int a1, .int a2, .int len2] m
      (fun r m' => r = some (.int (combine a1 a2 len2)) ∧ m.next ≤ m'.next ∧
        ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_cb := combine_lt a1 a2 len2
  cir_start
  cir_vcg

/-- `adler32_combine(adler1, adler2, len2)` from the module's initial memory. -/
def cRunCb (x : CbInput) : Res (Exit × Mem) :=
  evalCall ctx "adler32_combine" [.int x.1.val, .int x.2.1.val, .int x.2.2.val] module.initMem

/-- `adler32_combine64(adler1, adler2, len2)` from the module's initial memory. -/
def cRunCb64 (x : CbInput) : Res (Exit × Mem) :=
  evalCall ctx "adler32_combine64" [.int x.1.val, .int x.2.1.val, .int x.2.2.val] module.initMem

/-- A run that `Returns` the model's value is a `CTotal` run. -/
theorem ret_of_returns {sym : String} {args : List Val} {m : Mem} {v : Nat} {P : Mem → Prop}
    (h : Returns ctx sym args m (fun r m' => r = some (.int v) ∧ P m')) :
    ∃ a, evalCall ctx sym args m = .ok a ∧ a.1 = .ret (some (.int (v : Int))) := by
  unfold Returns Calls at h
  obtain ⟨⟨e, m'⟩, ha, hq⟩ := Res.holds_ok_iff.mp h
  refine ⟨(e, m'), ha, ?_⟩
  cases e with
  | ret r => exact congrArg Exit.ret (And.left hq)
  | _ => exact absurd hq id

theorem ctotal_cb : CTotal cbLong cbModel cRunCb := by
  intro x _
  have h1 := x.1.hBounds
  have h2 := x.2.1.hBounds
  have h3 := x.2.2.hBounds
  simp only [UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq] at h1 h2 h3
  exact ret_of_returns (adler32_combine_spec x.1.val x.2.1.val x.2.2.val module.initMem h1 h2 (by omega))

theorem ctotal_cb64 : CTotal cbLong cbModel cRunCb64 := by
  intro x _
  have h1 := x.1.hBounds
  have h2 := x.2.1.hBounds
  have h3 := x.2.2.hBounds
  simp only [UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq] at h1 h2 h3
  exact ret_of_returns (adler32_combine64_spec x.1.val x.2.1.val x.2.2.val module.initMem h1 h2 (by omega))

end EquivLean.Demo.XLang.Adler32.C
