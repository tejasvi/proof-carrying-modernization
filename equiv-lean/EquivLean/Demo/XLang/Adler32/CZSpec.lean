import EquivLean.Demo.XLang.Adler32.CZ
import EquivLean.Demo.XLang.Adler32.CCombineSpec
import EquivLean.Demo.XLang.Adler32.ModelLemmas

/-!
# zlib adler32 → model, C side: `adler32` and the runs of `adler32_z` and `adler32`

* `adler32_buf`, `adler32_null`, `adler32_null_one`: `adler32(adler, buf, len)` (`len` a `uInt`) calls
  `adler32_z(adler, buf, len)` (`CZ`'s contracts `adler32_z_buf`, `adler32_z_null`, `adler32_z_null_one`).
* `cRunZ`, `cRun32`: the runs of `adler32_z` and `adler32` on the Rust side's input `x : ZInput` (the buffer's bytes
  as block 0 of `cMem`, or `Z_NULL` from the module's initial memory; `adler32` gets `len mod 2^32`).
* `cspec_z`, `cspec_32`: `CSpec zLong zModel`. `cub_z_iff`, `cub_32_iff`: off `zLong` the C run has undefined
  behaviour exactly on `Z_NULL` with `len = 1`, and returns on every other input.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Adler32.Adler32 (ctx module)
open EquivLean.Demo.XLang.Adler32 (adler32z)

set_option maxHeartbeats 4000000

namespace EquivLean.Demo.XLang.Adler32.C

attribute [cir_spec] adler32_z_buf adler32_z_null

set_option cir.inline false in
/-- `adler32(adler, buf, len)` on a buffer of `len` bytes: `adler32_z(adler, buf, len)`. -/
@[cir_spec]
theorem adler32_buf (a0 : Nat) (bs : List Nat) (m : Mem) (bb : Nat) (hbb : bb < m.next)
    (hm : m.blocks bb = some ⟨.readonly, true, .array (.int false 8) bs.length, .arr (bs.map fun b : Nat => Val.int b)⟩)
    (ha : a0 < 2 ^ 64) (hbs : ∀ b ∈ bs, b < 256) (hl : bs.length < 2 ^ 28) :
    Returns ctx "adler32" [.int a0, .ptr (.loc bb [.idx 0]), .int bs.length] m
      (fun r m' => r = some (.int (adler32z a0 (some bs))) ∧ m.next ≤ m'.next ∧
        ∀ b < m.next, m'.blocks b = m.blocks b) := by
  have cirH_z := adler32z_lt a0 bs hbs
  cir_start
  cir_vcg

set_option cir.inline false in
/-- `adler32(adler, Z_NULL, len)` for `len ≠ 1`: 1. -/
@[cir_spec]
theorem adler32_null (a0 len : Nat) (m : Mem) (ha : a0 < 2 ^ 64) (hlen : len < 2 ^ 32) (h1 : len ≠ 1) :
    Returns ctx "adler32" [.int a0, .ptr .null, .int len] m
      (fun r m' => r = some (.int 1) ∧ m.next ≤ m'.next ∧ ∀ b < m.next, m'.blocks b = m.blocks b) := by
  cir_start
  cir_vcg

/-- `adler32(adler, Z_NULL, 1)` does not return: `adler32_z` reads `buf[0]`. -/
theorem adler32_null_one (a0 : Nat) (m : Mem) (ha : a0 < 2 ^ 64) :
    pholds (evalCall ctx "adler32" [.int a0, .ptr .null, .int 1] m) (fun _ => False) := by
  intro r hr
  have hs0 := holds_of_eq_ok hr
  cir_hstep hs0
  cir_hrun_c hs0
  obtain ⟨_, _, hF, _⟩ :=
    holds_pspec_elim (P := fun _ => False) hs0 (fun a h => adler32_z_null_one _ _ ha a h)
  exact hF

/-! ### The runs on the Rust side's inputs -/

open Aeneas.Std
open EquivLean.Demo.XLang.Adler32 (ZInput zLen zLong zModel bytesOf CSpec CUB)

/-- `adler32_z(adler, buf, len)` on the Rust side's input (`cRun`: the buffer's bytes as block 0 of `cMem`, `len`
their number; or `Z_NULL` with `len`, from the module's initial memory). -/
def cRunZ (x : ZInput) : Res (Exit × Mem) := cRun x.1.val (x.2.1.map bytesOf) (zLen x).val

/-- `adler32(adler, buf, len)` on the Rust side's input, `len` passed as a `uInt` (`len mod 2^32`). -/
def cRun32 (x : ZInput) : Res (Exit × Mem) :=
  match x.2.1 with
  | some b => evalCall ctx "adler32" [.int x.1.val, .ptr (.loc 0 [.idx 0]), .int ((zLen x).val % 2 ^ 32 : Nat)]
      (cMem (bytesOf b))
  | none => evalCall ctx "adler32" [.int x.1.val, .ptr .null, .int ((zLen x).val % 2 ^ 32 : Nat)] module.initMem

theorem bytesOf_lt (b : Slice U8) : ∀ v ∈ bytesOf b, v < 256 := by
  intro v hv
  simp only [bytesOf, List.mem_map] at hv
  obtain ⟨u, -, rfl⟩ := hv
  have := u.hBounds
  simp only [UScalarTy.U8_numBits_eq] at this
  omega

theorem bytesOf_length (b : Slice U8) : (bytesOf b).length = (Slice.len b).val := by
  simp only [bytesOf, List.length_map, Slice.len_val]

theorem cRunZ_buf (adler : U64) (b : Slice U8) (len : Usize) (hl : (Slice.len b).val < 2 ^ 28) :
    ∃ a, cRunZ (adler, some b, len) = .ok a ∧ a.1 = .ret (some (.int (zModel (adler, some b, len) : Int))) := by
  have ha := adler.hBounds
  simp only [UScalarTy.U64_numBits_eq] at ha
  exact ret_of_returns (adler32_z_buf adler.val (bytesOf b) (cMem (bytesOf b)) 0 (by rw [cMem_next]; omega)
    (cMem_blocks0 _) ha (bytesOf_lt b) (by rw [bytesOf_length]; exact hl))

theorem cRunZ_null (adler : U64) (len : Usize) (h1 : len.val ≠ 1) (hl : len.val < 2 ^ 28) :
    ∃ a, cRunZ (adler, none, len) = .ok a ∧ a.1 = .ret (some (.int (zModel (adler, none, len) : Int))) := by
  have ha := adler.hBounds
  simp only [UScalarTy.U64_numBits_eq] at ha
  exact ret_of_returns (v := 1) (adler32_z_null adler.val len.val module.initMem ha (by omega) h1)

theorem cRunZ_null_one (adler : U64) (len : Usize) (h1 : len.val = 1) : ∀ a, cRunZ (adler, none, len) ≠ .ok a := by
  intro a h
  have ha := adler.hBounds
  simp only [UScalarTy.U64_numBits_eq] at ha
  have h' : evalCall ctx "adler32_z" [.int adler.val, .ptr .null, .int len.val] module.initMem = .ok a := h
  rw [h1] at h'
  exact adler32_z_null_one adler.val module.initMem ha a h'

theorem cRun32_buf (adler : U64) (b : Slice U8) (len : Usize) (hl : (Slice.len b).val < 2 ^ 28) :
    ∃ a, cRun32 (adler, some b, len) = .ok a ∧ a.1 = .ret (some (.int (zModel (adler, some b, len) : Int))) := by
  have ha := adler.hBounds
  simp only [UScalarTy.U64_numBits_eq] at ha
  have hmod : (Slice.len b).val % 2 ^ 32 = (bytesOf b).length := by rw [bytesOf_length]; omega
  have h := ret_of_returns (adler32_buf adler.val (bytesOf b) (cMem (bytesOf b)) 0 (by rw [cMem_next]; omega)
    (cMem_blocks0 _) ha (bytesOf_lt b) (by rw [bytesOf_length]; exact hl))
  show ∃ a, evalCall ctx "adler32"
      [.int adler.val, .ptr (.loc 0 [.idx 0]), .int ((Slice.len b).val % 2 ^ 32 : Nat)]
      (cMem (bytesOf b)) = .ok a ∧ a.1 = .ret (some (.int (adler32z adler.val (some (bytesOf b)) : Int)))
  rw [hmod]
  exact h

theorem cRun32_null (adler : U64) (len : Usize) (h1 : len.val % 2 ^ 32 ≠ 1) :
    ∃ a, cRun32 (adler, none, len) = .ok a ∧ a.1 = .ret (some (.int (zModel (adler, none, len) : Int))) := by
  have ha := adler.hBounds
  simp only [UScalarTy.U64_numBits_eq] at ha
  exact ret_of_returns (v := 1)
    (adler32_null adler.val (len.val % 2 ^ 32) module.initMem ha (Nat.mod_lt _ (by decide)) h1)

theorem cRun32_null_one (adler : U64) (len : Usize) (h1 : len.val % 2 ^ 32 = 1) :
    ∀ a, cRun32 (adler, none, len) ≠ .ok a := by
  intro a h
  have ha := adler.hBounds
  simp only [UScalarTy.U64_numBits_eq] at ha
  have h' : evalCall ctx "adler32" [.int adler.val, .ptr .null, .int (len.val % 2 ^ 32 : Nat)] module.initMem =
    .ok a := h
  rw [h1] at h'
  exact adler32_null_one adler.val module.initMem ha a h'

/-- **`adler32_z`**: off the large inputs, a C run that returns has the model's value. -/
theorem cspec_z : CSpec zLong zModel cRunZ := by
  rintro ⟨adler, buf, len⟩ a hlong hrun
  have hl : (zLen (adler, buf, len)).val < 2 ^ 28 := by simp only [zLong, not_le] at hlong; exact hlong
  cases buf with
  | some b =>
    obtain ⟨a', ha', hr⟩ := cRunZ_buf adler b len hl
    rw [ha'] at hrun; cases hrun; exact hr
  | none =>
    by_cases h1 : len.val = 1
    · exact absurd hrun (cRunZ_null_one adler len h1 a)
    · obtain ⟨a', ha', hr⟩ := cRunZ_null adler len h1 hl
      rw [ha'] at hrun; cases hrun; exact hr

/-- **`adler32`** (`len` as a `uInt`): off the large inputs, a C run that returns has the model's value. -/
theorem cspec_32 : CSpec zLong zModel cRun32 := by
  rintro ⟨adler, buf, len⟩ a hlong hrun
  have hl : (zLen (adler, buf, len)).val < 2 ^ 28 := by simp only [zLong, not_le] at hlong; exact hlong
  cases buf with
  | some b =>
    obtain ⟨a', ha', hr⟩ := cRun32_buf adler b len hl
    rw [ha'] at hrun; cases hrun; exact hr
  | none =>
    by_cases h1 : len.val % 2 ^ 32 = 1
    · exact absurd hrun (cRun32_null_one adler len h1 a)
    · obtain ⟨a', ha', hr⟩ := cRun32_null adler len h1
      rw [ha'] at hrun; cases hrun; exact hr

/-- Off the large inputs, the C run of `adler32_z` has undefined behaviour exactly on `Z_NULL` with `len = 1` (it
reads `buf[0]`); on every other input it returns (`cspec_z` gives its value). -/
theorem cub_z_iff (x : ZInput) (hlong : ¬ zLong x) : CUB cRunZ x ↔ x.2.1 = none ∧ (zLen x).val = 1 := by
  obtain ⟨adler, buf, len⟩ := x
  have hl : (zLen (adler, buf, len)).val < 2 ^ 28 := by simp only [zLong, not_le] at hlong; exact hlong
  unfold CUB
  rw [safe_res]
  cases buf with
  | some b =>
    obtain ⟨a, ha, -⟩ := cRunZ_buf adler b len hl
    exact ⟨fun h => (h ⟨a, ha⟩).elim, fun h => (Option.some_ne_none b h.1).elim⟩
  | none =>
    by_cases h1 : len.val = 1
    · exact ⟨fun _ => ⟨rfl, h1⟩, fun _ ⟨a, ha⟩ => cRunZ_null_one adler len h1 a ha⟩
    · obtain ⟨a, ha, -⟩ := cRunZ_null adler len h1 hl
      exact ⟨fun h => (h ⟨a, ha⟩).elim, fun h => (h1 h.2).elim⟩

/-- Off the large inputs, the C run of `adler32` has undefined behaviour exactly on `Z_NULL` with `len = 1`; on
every other input it returns (`cspec_32` gives its value). -/
theorem cub_32_iff (x : ZInput) (hlong : ¬ zLong x) : CUB cRun32 x ↔ x.2.1 = none ∧ (zLen x).val = 1 := by
  obtain ⟨adler, buf, len⟩ := x
  have hl : (zLen (adler, buf, len)).val < 2 ^ 28 := by simp only [zLong, not_le] at hlong; exact hlong
  unfold CUB
  rw [safe_res]
  cases buf with
  | some b =>
    obtain ⟨a, ha, -⟩ := cRun32_buf adler b len hl
    exact ⟨fun h => (h ⟨a, ha⟩).elim, fun h => (Option.some_ne_none b h.1).elim⟩
  | none =>
    have hl' : len.val < 2 ^ 28 := hl
    have hmod : len.val % 2 ^ 32 = len.val := Nat.mod_eq_of_lt (by omega)
    by_cases h1 : len.val = 1
    · exact ⟨fun _ => ⟨rfl, h1⟩, fun _ ⟨a, ha⟩ => cRun32_null_one adler len (by rw [hmod]; exact h1) a ha⟩
    · obtain ⟨a, ha, -⟩ := cRun32_null adler len (by rw [hmod]; exact h1)
      exact ⟨fun h => (h ⟨a, ha⟩).elim, fun h => (h1 h.2).elim⟩

end EquivLean.Demo.XLang.Adler32.C
