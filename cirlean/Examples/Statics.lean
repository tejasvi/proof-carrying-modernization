import CIR
import Examples.Gen.Statics
import Examples.GenM.Statics

/-!
  A function that writes a function-local static array
  (`Examples/cpp/statics.cpp`). ClangIR emits the static as a module global,
  `_ZZ4bumpE7counter`; `ctx.gaddr sym` is the block of a global. A contract
  describes the static's block in an arbitrary memory: its kind, type and
  contents, here an element fact `vs[k]? = some v` and the bound needed for
  the increment.

  `bump_spec` is stated for the concrete module (the static is block 0);
  `bump_spec_mod` for any context that contains `bump`, with the static at
  some block `b` (`ctx.gaddr "_ZZ4bumpE7counter" = some b`), as in a
  per-function proof (`cir2lean --modular`, `Examples/GenM/Statics/`).
-/

open CIR Gen.Statics

set_option maxHeartbeats 4000000

namespace Examples.Statics

/-- `bump(k)` increments element `k` of its static array and returns a
pointer to it; only that block changes. -/
theorem bump_spec (vs : List Int) (k v : Int) (m : Mem) (kd : BlockKind)
    (hb : m.blocks 0 = some ⟨kd, true, .array (.int true 32) 4, .arr (vs.map .int)⟩)
    (hkd : kd ≠ .readonly) (hn : 1 ≤ m.next) (hlen : vs.length = 4)
    (hk : 0 ≤ k ∧ k < 4) (hv : vs[k.toNat]? = some v) (hvr : -2147483648 ≤ v ∧ v < 2147483647) :
    Returns ctx "bump" [.int k] m (fun r m' =>
      r = some (.ptr (.loc 0 [.idx k.toNat])) ∧
      m'.blocks 0 = some ⟨kd, true, .array (.int true 32) 4,
        .arr ((vs.map .int).set k.toNat (.int (v + 1)))⟩ ∧
      Frame m m' [0]) := by
  cir_start
  cir_vcg

/-- `bump` in any context that contains it, with its static at block `b`. -/
theorem bump_spec_mod (ctx : Ctx)
    (hf : ctx.mod.findFunc? "bump" = some Examples.GenM.Statics.fn_bump)
    (b : Nat) (hg : ctx.gaddr "_ZZ4bumpE7counter" = some b)
    (vs : List Int) (k v : Int) (m : Mem) (kd : BlockKind)
    (hb : m.blocks b = some ⟨kd, true, .array (.int true 32) 4, .arr (vs.map .int)⟩)
    (hkd : kd ≠ .readonly) (hn : b < m.next) (hlen : vs.length = 4)
    (hk : 0 ≤ k ∧ k < 4) (hv : vs[k.toNat]? = some v) (hvr : -2147483648 ≤ v ∧ v < 2147483647) :
    Returns ctx "bump" [.int k] m (fun r m' =>
      r = some (.ptr (.loc b [.idx k.toNat])) ∧
      m'.blocks b = some ⟨kd, true, .array (.int true 32) 4,
        .arr ((vs.map .int).set k.toNat (.int (v + 1)))⟩ ∧
      Frame m m' [b]) := by
  cir_start
  cir_vcg

/-- The modular contract in the module of `statics.cpp`: `cir_lookup` gives
the function and the static's block. -/
example (vs : List Int) (k v : Int) (m : Mem) (kd : BlockKind)
    (hb : m.blocks 0 = some ⟨kd, true, .array (.int true 32) 4, .arr (vs.map .int)⟩)
    (hkd : kd ≠ .readonly) (hn : 0 < m.next) (hlen : vs.length = 4)
    (hk : 0 ≤ k ∧ k < 4) (hv : vs[k.toNat]? = some v) (hvr : -2147483648 ≤ v ∧ v < 2147483647) :
    Returns Examples.GenM.Statics.ctx "bump" [.int k] m (fun r m' =>
      r = some (.ptr (.loc 0 [.idx k.toNat])) ∧
      m'.blocks 0 = some ⟨kd, true, .array (.int true 32) 4,
        .arr ((vs.map .int).set k.toNat (.int (v + 1)))⟩ ∧
      Frame m m' [0]) :=
  bump_spec_mod _ (by cir_lookup) 0 (by cir_lookup) vs k v m kd hb hkd hn hlen hk hv hvr

end Examples.Statics
