/-
# Binary items at the bit level, for `bv_decide`

`COMP-5` items (and `COMP` / `BINARY` under `TRUNC(BIN)`) are two's-complement machine
integers, like Java's `short` / `int` / `long` and Rust's `i16` / `i32` / `i64`.  A rewrite
typically reads and writes them with shifts and masks (`ByteBuffer`, `from_be_bytes`) and
relies on wrap-around arithmetic, sign extension (`short` used in `int` arithmetic) and
narrowing casts.  Such programs are equivalent bit for bit, which is what `bv_decide`
decides (bit-blasting to SAT; the LRAT certificate is checked by the kernel).

This file restates the COBOL side in `BitVec` terms (simp set `cobol_bits`):

* `decBinary` (big-endian, `n` bytes) is `(BitVec.ofNat (8n) value).toInt` (or `toNat`);
* `encBinary` writes the big-endian bytes of `BitVec.ofInt (8n) v`;
* binary truncation (`fitBin`, `wrapBin`) disappears under `BitVec.ofInt` at the item's width,
  and becomes sign extension at a larger width;

and models the byte-level reads and writes of Java (`Java.Bits`, = Rust's `from_be_bytes` /
`to_be_bytes`).  After symbolic execution, `cobol_bv` rewrites with these lemmas and calls
`bv_decide`.  (Big-endian storage, as on IBM; `Config.comp5LE` / `binaryLE` are the GnuCOBOL
little-endian variants.)
-/
import Std.Tactic.BVDecide
import Cobol.Logic.Eval

namespace Cobol.Bits
open Digits

/-! ## Decoding and encoding -/

theorem ofDigits_lt_binMod (n : Nat) (bs : List UInt8) (hl : bs.length = n) :
    ofDigits 256 (bs.map UInt8.toNat) < binMod n := by
  rw [← pow256]
  have := ofDigits_lt (b := 256) (by decide) (bs.map UInt8.toNat)
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨b, _, rfl⟩ := hx; exact b.toNat_lt)
  simpa [hl] using this

@[cobol_bits] theorem decBinary_be_signed (n : Nat) (bs : List UInt8) (hl : bs.length = n)
    (hn : 0 < n) :
    decBinary false n true bs = (BitVec.ofNat (8 * n) (ofDigits 256 (bs.map UInt8.toNat))).toInt := by
  unfold decBinary
  simp only [Bool.false_eq_true, ↓reduceIte, true_and]
  have hlt := ofDigits_lt_binMod n bs hl
  have h2 := binMod_eq_two_mul hn
  have hm : binMod n = 2 ^ (8 * n) := rfl
  have hc : ((2 : Int) ^ (8 * n)) = ((binMod n : Nat) : Int) := by rw [hm]; push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> split <;> push_cast at * <;> omega

@[cobol_bits] theorem decBinary_be_unsigned (n : Nat) (bs : List UInt8) (hl : bs.length = n) :
    decBinary false n false bs =
      ((BitVec.ofNat (8 * n) (ofDigits 256 (bs.map UInt8.toNat))).toNat : Int) := by
  unfold decBinary
  simp only [Bool.false_eq_true, ↓reduceIte, false_and]
  have hlt := ofDigits_lt_binMod n bs hl
  have hm : binMod n = 2 ^ (8 * n) := rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

@[cobol_bits] theorem encBinary_be1 (v : Int) :
    encBinary false 1 v = [UInt8.ofBitVec (BitVec.ofInt 8 v)] := by
  simp only [encBinary, toDigits, binMod, Bool.false_eq_true, ↓reduceIte, List.nil_append,
    List.map_cons, List.map_nil, List.cons.injEq, and_true]
  apply UInt8.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
  simp only [UInt8.toBitVec_ofNat', BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

@[cobol_bits] theorem encBinary_be2 (v : Int) : encBinary false 2 v =
    [UInt8.ofBitVec ((BitVec.ofInt 16 v >>> 8).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 16 v).setWidth 8)] := by
  simp only [encBinary, toDigits, binMod, Bool.false_eq_true, ↓reduceIte, List.nil_append,
    List.cons_append, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_⟩ <;> apply UInt8.toBitVec_inj.mp <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [UInt8.toBitVec_ofNat', BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow] <;> omega

@[cobol_bits] theorem encBinary_be4 (v : Int) : encBinary false 4 v =
    [UInt8.ofBitVec ((BitVec.ofInt 32 v >>> 24).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 32 v >>> 16).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 32 v >>> 8).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 32 v).setWidth 8)] := by
  simp only [encBinary, toDigits, binMod, Bool.false_eq_true, ↓reduceIte, List.nil_append,
    List.cons_append, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toBitVec_inj.mp <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [UInt8.toBitVec_ofNat', BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow] <;> omega

@[cobol_bits] theorem encBinary_be8 (v : Int) : encBinary false 8 v =
    [UInt8.ofBitVec ((BitVec.ofInt 64 v >>> 56).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 64 v >>> 48).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 64 v >>> 40).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 64 v >>> 32).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 64 v >>> 24).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 64 v >>> 16).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 64 v >>> 8).setWidth 8),
     UInt8.ofBitVec ((BitVec.ofInt 64 v).setWidth 8)] := by
  simp only [encBinary, toDigits, binMod, Bool.false_eq_true, ↓reduceIte, List.nil_append,
    List.cons_append, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toBitVec_inj.mp <;>
    apply BitVec.eq_of_toNat_eq <;>
    simp only [UInt8.toBitVec_ofNat', BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow] <;> omega

/-! ## Truncation and widening -/

/-- Binary wrap-around is invisible at the item's width. -/
theorem ofInt_wrapBin (n : Nat) (s : Bool) (v : Int) :
    BitVec.ofInt (8 * n) (Sem.wrapBin n s v) = BitVec.ofInt (8 * n) v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  have hm : ((2 ^ (8 * n) : Nat) : Int) = (binMod n : Int) := rfl
  rw [hm]
  unfold Sem.wrapBin
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [Int.emod_emod]
  · rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod, Int.add_sub_cancel]

theorem ofInt_fitBin_snd (n : Nat) (s : Bool) (v : Int) :
    BitVec.ofInt (8 * n) (Sem.fitBin n s v).2 = BitVec.ofInt (8 * n) v := by
  unfold Sem.fitBin
  split
  · rfl
  · exact ofInt_wrapBin n s v

@[cobol_bits] theorem ofInt_fitBin1 (s : Bool) (v : Int) :
    BitVec.ofInt 8 (Sem.fitBin 1 s v).2 = BitVec.ofInt 8 v := ofInt_fitBin_snd 1 s v
@[cobol_bits] theorem ofInt_fitBin2 (s : Bool) (v : Int) :
    BitVec.ofInt 16 (Sem.fitBin 2 s v).2 = BitVec.ofInt 16 v := ofInt_fitBin_snd 2 s v
@[cobol_bits] theorem ofInt_fitBin4 (s : Bool) (v : Int) :
    BitVec.ofInt 32 (Sem.fitBin 4 s v).2 = BitVec.ofInt 32 v := ofInt_fitBin_snd 4 s v
@[cobol_bits] theorem ofInt_fitBin8 (s : Bool) (v : Int) :
    BitVec.ofInt 64 (Sem.fitBin 8 s v).2 = BitVec.ofInt 64 v := ofInt_fitBin_snd 8 s v

/-- A signed value stored in a narrower item, then used at a larger width: sign extension
(Java's `short` → `int` promotion). -/
@[cobol_bits] theorem ofInt_fitBin2_32 (v : Int) :
    BitVec.ofInt 32 (Sem.fitBin 2 true v).2 = (BitVec.ofInt 16 v).signExtend 32 := by
  apply BitVec.toInt_inj.mp
  simp only [BitVec.toInt_ofInt, BitVec.toInt_signExtend, Sem.fitBin, Sem.inBinRange, Sem.wrapBin,
    binHalf, binMod, Int.bmod_def]
  by_cases h : -32768 ≤ v ∧ v < 32768
  · simp [h] <;> split <;> split <;> omega
  · simp [h] <;> split <;> split <;> omega

@[cobol_bits] theorem ofInt_fitBin2_64 (v : Int) :
    BitVec.ofInt 64 (Sem.fitBin 2 true v).2 = (BitVec.ofInt 16 v).signExtend 64 := by
  apply BitVec.toInt_inj.mp
  simp only [BitVec.toInt_ofInt, BitVec.toInt_signExtend, Sem.fitBin, Sem.inBinRange, Sem.wrapBin,
    binHalf, binMod, Int.bmod_def]
  by_cases h : -32768 ≤ v ∧ v < 32768
  · simp [h] <;> split <;> split <;> omega
  · simp [h] <;> split <;> split <;> omega

@[cobol_bits] theorem ofInt_fitBin4_64 (v : Int) :
    BitVec.ofInt 64 (Sem.fitBin 4 true v).2 = (BitVec.ofInt 32 v).signExtend 64 := by
  apply BitVec.toInt_inj.mp
  simp only [BitVec.toInt_ofInt, BitVec.toInt_signExtend, Sem.fitBin, Sem.inBinRange, Sem.wrapBin,
    binHalf, binMod, Int.bmod_def]
  by_cases h : -2147483648 ≤ v ∧ v < 2147483648
  · simp [h] <;> split <;> split <;> omega
  · simp [h] <;> split <;> split <;> omega

/-- `BitVec.ofInt w x.toInt` is sign extension (the definition of `signExtend`). -/
@[cobol_bits] theorem ofInt_toInt_signExtend {w : Nat} (x : BitVec w) (v : Nat) :
    BitVec.ofInt v x.toInt = x.signExtend v := rfl

@[cobol_bits] theorem ofInt_ite (w : Nat) (c : Prop) [Decidable c] (a b : Int) :
    BitVec.ofInt w (if c then a else b) = if c then BitVec.ofInt w a else BitVec.ofInt w b := by
  split <;> rfl

@[cobol_bits] theorem uint8_toNat (b : UInt8) : b.toNat = b.toBitVec.toNat := rfl

attribute [cobol_bits] BitVec.ofInt_add BitVec.ofInt_mul BitVec.ofInt_neg BitVec.ofInt_toInt
  BitVec.ofNat_add BitVec.ofNat_mul BitVec.ofNat_toNat BitVec.ofInt_natCast
  ofDigits List.foldl_cons List.foldl_nil List.map_cons List.map_nil List.length_cons
  List.length_nil Nat.zero_mul Nat.zero_add UInt8.ofBitVec.injEq
  Int16.toBitVec_toInt32 Int16.toBitVec_ofBitVec Int16.toBitVec_add Int16.toBitVec_mul
  Int16.toBitVec_ofNat Int32.toBitVec_ofBitVec Int32.toBitVec_add Int32.toBitVec_mul
  Int32.toBitVec_ofNat Int64.toBitVec_ofBitVec Int64.toBitVec_add Int64.toBitVec_mul
  Int64.toBitVec_ofNat Int32.toBitVec_toInt64 Int16.toBitVec_toInt64

end Cobol.Bits

/-! ## Java: big-endian reads and writes (`ByteBuffer`, also Rust `from_be_bytes`) -/

namespace Java.Bits

/-- `(short) (((b0 & 0xFF) << 8) | (b1 & 0xFF))`, i.e. `ByteBuffer.getShort` (big-endian). -/
def getShort (b0 b1 : UInt8) : Int16 :=
  Int16.ofBitVec ((b0.toBitVec.setWidth 16 <<< 8) ||| b1.toBitVec.setWidth 16)

/-- `ByteBuffer.getInt` (big-endian). -/
def getInt (b0 b1 b2 b3 : UInt8) : Int32 :=
  Int32.ofBitVec ((b0.toBitVec.setWidth 32 <<< 24) ||| (b1.toBitVec.setWidth 32 <<< 16) |||
    (b2.toBitVec.setWidth 32 <<< 8) ||| b3.toBitVec.setWidth 32)

/-- `ByteBuffer.putShort`: `{ (byte) (s >> 8), (byte) s }`. -/
def putShort (s : Int16) : List UInt8 :=
  [UInt8.ofBitVec ((s.toBitVec.sshiftRight 8).setWidth 8), UInt8.ofBitVec (s.toBitVec.setWidth 8)]

/-- `ByteBuffer.putInt`. -/
def putInt (i : Int32) : List UInt8 :=
  [UInt8.ofBitVec ((i.toBitVec.sshiftRight 24).setWidth 8),
   UInt8.ofBitVec ((i.toBitVec.sshiftRight 16).setWidth 8),
   UInt8.ofBitVec ((i.toBitVec.sshiftRight 8).setWidth 8), UInt8.ofBitVec (i.toBitVec.setWidth 8)]

attribute [cobol_bits] getShort getInt putShort putInt

end Java.Bits

namespace Cobol

/-- Equivalence of programs over binary items: symbolic execution, restatement in `BitVec`
(`cobol_bits`), then `bv_decide`. -/
syntax "cobol_bv" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cobol_bv) => `(tactic| cobol_bv [])
  | `(tactic| cobol_bv [$xs,*]) =>
    `(tactic| (try cobol_sym [decodeNum, encodeNum, Sem.fitNum, length_encBinary, $xs,*]) <;>
      (try simp only [cobol_bits, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT,
        List.cons.injEq, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        and_true, List.length_cons, List.length_nil, Nat.zero_lt_succ, Nat.zero_lt_one]) <;>
      bv_decide)

end Cobol
