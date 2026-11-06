import EquivLean.Demo.Gen.Cir.Adler32.Adler32
import EquivLean.Demo.XLang.TinyRegex.CPartial
import EquivLean.Demo.XLang.Adler32.Model

/-!
# zlib adler32 → model, C side: shared definitions

* The 64-bit `unsigned long` operations of `adler32.c` on values below `2^64`, as the model writes them:
  `&` and `|` (cirlean's `bitwise`, through `BitVec`) are `Nat.land` / `Nat.lor`, `>>` is division by a power of
  two, `<<` is multiplication by one (`bw_and`, `bw_or`).
* The run: `cMem bs` (the module's initial memory, then the buffer `bs` as a read-only block of `unsigned char`s,
  block 0) and `cRun adler buf len`, the call `adler32_z(adler, buf, len)` with `buf` the buffer (`some bs`, `len =
  bs.length`) or `Z_NULL` (`none`).
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Adler32.Adler32 (ctx module)
open EquivLean.Demo.XLang.Adler32 (pack)

namespace EquivLean.Demo.XLang.Adler32.C

theorem bw_and (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    bitwise false 64 (fun a b => a &&& b) (x : Int) (y : Int) = ((x &&& y : Nat) : Int) := by
  unfold bitwise
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_and, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem bw_or (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    bitwise false 64 (fun a b => a ||| b) (x : Int) (y : Int) = ((x ||| y : Nat) : Int) := by
  unfold bitwise
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_or, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- `x & 0xffff` as the executor writes it. -/
theorem bw_and_ffff (x : Nat) (hx : x < 2 ^ 64) :
    bitwise false 64 (fun a b => a &&& b) (x : Int) 65535 = ((x &&& 0xffff : Nat) : Int) :=
  bw_and x 65535 hx (by decide)

theorem land_ffff (x : Nat) : x &&& 0xffff = x % 65536 := by
  rw [show (0xffff : Nat) = 2 ^ 16 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem shiftRight_16 (x : Nat) : x >>> 16 = x / 65536 := by
  rw [Nat.shiftRight_eq_div_pow]

theorem shiftLeft_16 (x : Nat) : x <<< 16 = x * 65536 := by
  rw [Nat.shiftLeft_eq]

/-- `x & 0xffff` as the executor writes it, as a remainder (for `omega`). -/
theorem bw_and_ffff_mod (x : Nat) (hx : x < 2 ^ 64) :
    bitwise false 64 (fun a b => a &&& b) (x : Int) 65535 = ((x % 65536 : Nat) : Int) := by
  rw [bw_and_ffff x hx, land_ffff]

/-- `(x >> 16) & 0xffff` as the executor writes it. -/
theorem bw_shr16_and (x : Nat) (hx : x < 2 ^ 64) :
    bitwise false 64 (fun a b => a &&& b) ((x : Int) / 65536) 65535 = ((x / 65536 % 65536 : Nat) : Int) := by
  rw [show (x : Int) / 65536 = ((x / 65536 : Nat) : Int) by omega]
  exact bw_and_ffff_mod _ (by omega)

/-- `|` on two `unsigned long` values. -/
theorem bw_or_int (x y : Int) (hx0 : 0 ≤ x) (hx : x < 2 ^ 64) (hy0 : 0 ≤ y) (hy : y < 2 ^ 64) :
    bitwise false 64 (fun a b => a ||| b) x y = ((x.toNat ||| y.toNat : Nat) : Int) := by
  have h := bw_or x.toNat y.toNat (by omega) (by omega)
  rwa [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0] at h

/-- The executor's range check of `x | y` (after `bw_or_int`) on two values below `2^64`. -/
theorem or_not_gt (a c : Nat) (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    ¬ (18446744073709551615 < ((a ||| c : Nat) : Int)) := by
  have := Nat.or_lt_two_pow ha hc
  omega

/-- `a | (s << 16)` as the executor leaves it. -/
theorem or_pack (a s : Int) (hs : 0 ≤ s) :
    a.toNat ||| (s * 65536).toNat = pack a.toNat s.toNat := by
  unfold pack
  rw [Nat.shiftLeft_eq]
  congr 1
  omega

/-- The memory of a run: the module's initial memory (no globals), then the buffer `bs` (block 0, read-only,
`bs.length` `unsigned char`s). -/
def cMem (bs : List Nat) : Mem :=
  (module.initMem.alloc .readonly (.array (.int false 8) bs.length) (.arr (bs.map fun b : Nat => Val.int b))).2

theorem initMem_eq : module.initMem = Mem.empty := by
  simp only [Module.initMem, module, Id.run, List.forIn_nil]
  rfl

theorem cMem_next (bs : List Nat) : (cMem bs).next = 1 := by
  simp only [cMem, initMem_eq, Mem.alloc, Mem.empty]

theorem cMem_blocks0 (bs : List Nat) :
    (cMem bs).blocks 0 =
      some ⟨.readonly, true, .array (.int false 8) bs.length, .arr (bs.map fun b : Nat => Val.int b)⟩ := by
  simp only [cMem, initMem_eq, Mem.alloc, Mem.empty, upd]
  rfl

/-- `adler32_z(adler, buf, len)`: `buf` the buffer `bs` (`len = bs.length`), or `Z_NULL` (`none`) with `len`. -/
def cRun (adler : Nat) : Option (List Nat) → Nat → Res (Exit × Mem)
  | some bs, _ => evalCall ctx "adler32_z" [.int adler, .ptr (.loc 0 [.idx 0]), .int bs.length] (cMem bs)
  | none, len => evalCall ctx "adler32_z" [.int adler, .ptr .null, .int len] module.initMem

end EquivLean.Demo.XLang.Adler32.C
