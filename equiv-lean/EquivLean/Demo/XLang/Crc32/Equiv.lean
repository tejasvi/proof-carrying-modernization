import EquivLean.Demo.XLang.Crc32.TS
import EquivLean.Demo.XLang.Crc32.Rust

/-!
# TypeScript ↔ Rust on real library code: pako's `crc32` ≡ crc32fast's baseline `update`

* TypeScript: pako 1.0.11's `lib/zlib/crc32.js` as TypeScript (`examples/ts/pako_crc32.ts`),
  translated by the pinned StrictTS front end (`Demo/Gen/TS/PakoCrc32.lean`): the table is
  computed when the module loads, then one loop over the bytes.
* Rust: crc32fast 1.4.2's baseline implementation (`examples/rust/crc32fast_base`, unmodified but
  for the module path), translated by Charon + Aeneas (`Demo/Gen/Aeneas/Crc32Base`): slice-by-16,
  unrolled four times, over a 16 × 256 constant table, then a byte loop over the rest.

The loops do not correspond (one byte per iteration against 64), so the two are not paired in
lockstep: each side is proved equal to zlib's CRC-32 (`Demo/XLang/Crc32/Spec.lean`;
`TS.crc32_spec`, `Rust.update_fast_16_eq`), and the equivalence follows (`crc32_equiv`).  The
outcome relation `CrcRel`: the TypeScript call returns the number holding the Rust `u32` as a
signed 32-bit value (pako returns `crc ^ -1` without `>>> 0`) and leaves the world unchanged;
neither side fails on any input (no panic, no exception, no divergence).
-/

namespace EquivLean.Demo.Crc32

open StrictTS EquivLean.TS
open _root_.Aeneas _root_.Aeneas.Std
open EquivLean.Demo.Gen.TS

/-- The outcome relation (see the module doc). -/
def CrcRel (w : World TS.TT) (o : EquivLean.TS.Out TS.TT (Val TS.TT .num)) (r : Except Error U32) :
    Prop :=
  ∃ h : U32, r = .ok h ∧ o = (.ok (.num (F64.ofInt32 h.bv)), w)

/-- **pako's `crc32` ≡ crc32fast's `update_fast_16`, on every input**: in a world whose global
`crcTable` holds pako's table (`TS.initWorld`: after the module's first statement), for every
starting value (`crc` a number whose ToInt32 is the Rust `prev`), every `Uint8Array` range
`[pos, pos + len)` and the Rust slice holding the same bytes. -/
theorem crc32_equiv (I : Impl) (w : World TS.TT) (ta b : Nat) (bytes : Array (BitVec 8))
    (len pos : Nat)
    (hg : w.heap.get? (.box (.arr .num), PakoCrc32.g_crcTable.idx) = some (some (.arr ta)))
    (ht : w.heap.get? (.arr .num, ta) = some TS.crcTable)
    (hb : w.heap.get? (.tarr .u8, b) = some bytes)
    (hpl : pos + len ≤ bytes.size) (hsz : bytes.size < 4294967296)
    (crc : F64) (prev : U32) (hcrc : crc.toInt32 = prev.bv)
    (buf : Slice U8) (hbuf : buf.val.map (·.bv) = (bytes.extract pos (pos + len)).toList) :
    Equiv (CrcRel w)
      (call I PakoCrc32.program PakoCrc32.crc32Ref
        (.cons (.num crc) (.cons (.tarr b) (.cons (.num (F64.ofNat len))
          (.cons (.num (F64.ofNat pos)) .nil)))) w)
      (crc32fast_base.update_fast_16 prev buf) := by
  have hts := TS.crc32_spec I w crc ta b bytes len pos hg ht hb hpl hsz
  have hrs := Rust.update_fast_16_eq prev buf
  rw [hbuf, ← hcrc] at hrs
  simp only [call]
  rw [hts, hrs]
  refine ⟨?_, ?_⟩
  · rw [sim_iff_of_runs (EquivLean.Aeneas.safe_ok _) ((EquivLean.Aeneas.runs_ok_iff _ _).2 rfl),
      wp_some]
    exact ⟨_, rfl, rfl⟩
  · rw [sim_iff_of_runs (s := some _) rfl rfl, EquivLean.Aeneas.wp_ok]
    exact ⟨_, rfl, rfl⟩

/-- The same after pako's module initialization (`TS.initWorld w`: its first statement builds the
table), from the number holding the Rust `u32` (`crc = prev`), for a whole `Uint8Array`. -/
theorem crc32_equiv_init (I : Impl) (w : World TS.TT) (b : Nat) (bytes : Array (BitVec 8))
    (hb : w.heap.get? (.tarr .u8, b) = some bytes) (hsz : bytes.size < 4294967296)
    (prev : U32) (buf : Slice U8) (hbuf : buf.val.map (·.bv) = bytes.toList) :
    Equiv (CrcRel (TS.initWorld w))
      (call I PakoCrc32.program PakoCrc32.crc32Ref
        (.cons (.num (F64.ofUint32 prev.bv)) (.cons (.tarr b) (.cons (.num (F64.ofNat bytes.size))
          (.cons (.num (F64.ofNat 0)) .nil)))) (TS.initWorld w))
      (crc32fast_base.update_fast_16 prev buf) :=
  crc32_equiv I (TS.initWorld w) w.next b bytes bytes.size 0 (TS.initWorld_global w)
    (TS.initWorld_table w) (by rw [TS.initWorld_tarr]; exact hb) (by omega) hsz _ prev
    (F64.toInt32_ofUint32 _) buf (by rw [hbuf, Nat.zero_add, Array.extract_size])

end EquivLean.Demo.Crc32

#print axioms EquivLean.Demo.Crc32.crc32_equiv
#print axioms EquivLean.Demo.Crc32.crc32_equiv_init
