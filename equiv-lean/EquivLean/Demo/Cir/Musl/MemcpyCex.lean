import EquivLean.Demo.Cir.Musl.Partial
import EquivLean.Demo.Cir.Musl.Gen.Memcpy

/-!
# musl `memcpy` does not refine cirlean's `memcpy` model: a counterexample

A finding about cirlean, not musl. cirlean has no byte-level memory. musl's word copy
`*(u32 *)(d+0) = *(u32 *)(s+0)` (`__may_alias__`) on `char` arrays therefore has no faithful meaning
there.

Concretely, copy the 7 characters 1..7 into 7 zero characters with `n = 7`, both pointers at
index 0. cirlean encodes `(uintptr_t)&x[i]` as `(b + 1) * 2^32 + (i + 1)`, so the head loop
copies 3 bytes until `(uintptr_t)s % 4 = 0`. `d` is then 4-aligned too, and `n & 4` copies "a
word" through `uint32_t` pointers at a `char` element.

* Up to cirlean 28e2380 (266d1ed), that word copy read and wrote the one element (`loadTy`/`storeTy`
  only checked that the value fits), so musl left `1 2 3 4 0 0 0` (proved at equivlean 65c47df). This
  finding led to cirlean's punning2 (2d65713).
* From punning2 on (this file is checked at cirlean `next`), a scalar access whose type does not match
  the element it reaches is undefined (`Mem.punnedAccess`). GCC defines musl's word copy through
  `__may_alias__`, but in cirlean musl's word paths are now undefined behaviour: the run has no outcome
  (`musl_memcpy_cex_ub`).

In both semantics the model copies all seven characters, so the outcomes differ
(`musl_memcpy_ne_model`).
-/

open CIR EquivLean.Cir

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace EquivLean.Demo.Cir.Musl

open EquivLean.Demo.Cir.Musl.Gen.Memcpy (ctx)

/-- `(uintptr_t)p % 4` for a pointer into the array block `b`: cirlean encodes the pointer as
`(b + 1) * 2^32 + c` (`evalCast .ptrToInt`, `c` from the path), so only `c` matters. -/
theorem p2i_mod4 (b : Nat) (c : Int) :
    (wrap false 64 (((b : Int) + 1) * 4294967296 + c)).tmod 4 = c % 4 := by
  unfold wrap
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  have h1 : 0 ≤ (((b : Int) + 1) * 4294967296 + c) % (2 : Int) ^ 64 := Int.emod_nonneg _ (by decide)
  rw [Int.tmod_eq_emod_of_nonneg h1, Int.emod_emod_of_dvd _ (by decide : (4 : Int) ∣ 2 ^ 64)]
  omega

/-- The source characters `1 .. 7`. -/
def cexSrc : List Val := [1, 2, 3, 4, 5, 6, 7].map fun (c : Int) => .int c

/-- The destination before the copy: seven zeros. -/
def cexDst : List Val := List.replicate 7 (.int 0)

/-- musl's `memcpy(d, s, 7)` on the counterexample has no outcome at cirlean `next`: after the three
bytes of the head loop, the word copy `*(u32 *)(d+0) = *(u32 *)(s+0)` is a `uint32_t` access to a
`char` element, which punning2 makes undefined. -/
theorem musl_memcpy_cex_ub (bs bd : Nat) (ks kd : BlockKind) (m : Mem)
    (hs : m.blocks bs = some ⟨ks, true, .array (.int true 8) 7, .arr cexSrc⟩)
    (hd : m.blocks bd = some ⟨kd, true, .array (.int true 8) 7, .arr cexDst⟩) (_hkd : kd ≠ .readonly)
    (hbs : bs < m.next) (hbd : bd < m.next) (hseg : m.next < 2 ^ 29) (hsd : bs ≠ bd) :
    ∀ r, evalCall ctx "musl_memcpy" [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 7] m ≠ .ok r := by
  intro r hr
  have hs0 := holds_of_eq_ok hr
  have cirH_bs := hs
  have cirH_bd := hd
  have cirH_sd : bs ≠ bd := hsd
  have cirH_p2s : (wrap false 64 (addrOfChar bs 0)).tmod 4 = 0 := tmod4_addrOfChar_flat (by omega) 0
  have cirH_p2d : (wrap false 64 (addrOfChar bd 0)).tmod 4 = 0 := tmod4_addrOfChar_flat (by omega) 0
  have cirH_n0 : ((0 : Int) != 0) = false := by decide
  have cirH_n4 : ((4 : Int) != 0) = true := by decide
  have cirH_b8 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 7 8 = 0 := by decide
  have cirH_b4 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 7 4 = 4 := by decide
  simp only [cexSrc, cexDst, List.map, List.replicate] at hs hd
  cir_hstep hs0
  cir_hrun_c hs0
  rw [evalFor_unfold] at hs0
  cir_hrun_c hs0
  rw [evalFor_unfold] at hs0
  cir_hrun_c hs0

theorem typedRange_fst {ctx : Ctx} {m : Mem} {b : Nat} {p : List PathElem} {n : Int}
    {r : Nat × List PathElem × Option Nat × Nat × Ty}
    (h : Std.typedRange? ctx m (.loc b p) n = some r) : r.1 = b := by
  unfold Std.typedRange? at h
  dsimp only at h
  repeat' (first | (cases h; done) | (cases h; rfl) | split at h)

theorem blockOffset?_fst {ctx : Ctx} {m : Mem} {b : Nat} {p : List PathElem} {r : Nat × Nat}
    (h : Std.blockOffset? ctx m (.loc b p) = some r) : r.1 = b := by
  unfold Std.blockOffset? at h
  dsimp only at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  · cases h

theorem runModel_memcpy_of_ne (ctx' : Ctx) (m : Mem) (bd bs : Nat) (pd ps : List PathElem) (n : Int)
    (hsd : bs ≠ bd) :
    Std.runModel ctx' .memcpy [.ptr (.loc bd pd), .ptr (.loc bs ps), .int n] m =
      Std.memcpyModel ctx' m (.loc bd pd) (.loc bs ps) n := by
  change (if Std.memcpyOverlap ctx' m (.loc bd pd) (.loc bs ps) n then _ else _) = _
  have h : Std.memcpyOverlap ctx' m (.loc bd pd) (.loc bs ps) n = false := by
    unfold Std.memcpyOverlap
    split
    · rfl
    · split
      · rename_i rs rd hrs hrd
        have hs1 := typedRange_fst hrs
        have hd1 := typedRange_fst hrd
        rcases rs with ⟨b1, p1, ip1, k1, t1⟩
        rcases rd with ⟨b2, p2, ip2, k2, t2⟩
        dsimp only at hs1 hd1
        subst hs1 hd1
        simp [Std.rangesOverlap, hsd]
      · unfold Std.bytesOverlap
        split
        · rename_i b1 x1 b2 y2 hr1 hr2
          have h1 := blockOffset?_fst hr1
          have h2 := blockOffset?_fst hr2
          dsimp only at h1 h2
          subst h1 h2
          simp [hsd.symm]
        · rfl
  simp [h]

/-- cirlean's `memcpy` model on the counterexample: the destination gets all seven characters. -/
theorem memcpy_model_cex (ctx' : Ctx) (bs bd : Nat) (ks kd : BlockKind) (m : Mem)
    (hs : m.blocks bs = some ⟨ks, true, .array (.int true 8) 7, .arr cexSrc⟩)
    (hd : m.blocks bd = some ⟨kd, true, .array (.int true 8) 7, .arr cexDst⟩) (hkd : kd ≠ .readonly) (hsd : bs ≠ bd) :
    Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 7] m =
      .ok (.ret (some (.ptr (.loc bd [.idx 0]))),
        m.setBlock bd ⟨kd, true, .array (.int true 8) 7, .arr cexSrc⟩) := by
  have h' : Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 7] m =
      Std.memcpyModel ctx' m (.loc bd [.idx 0]) (.loc bs [.idx 0]) 7 := runModel_memcpy_of_ne ctx' m bd bs [.idx 0] [.idx 0] 7 hsd
  rw [h']
  simp [Std.memcpyModel, Std.typedRange?, splitLast, Ctx.typeAt, Ctx.sizeAlign, Mem.read?, Mem.live?, hs, hd,
    Val.get?, Std.rangeVals, Std.rangeWrite, Mem.write?, Val.set?, hkd, Std.retv, cexSrc, cexDst, wrap]

/-- **Counterexample:** on these inputs musl's `memcpy` and cirlean's `memcpy` model have different
outcomes. The model copies `1 .. 7`; musl's run has no outcome at cirlean `next` (its word copy is a
type-punned access; up to 28e2380 it left `1 2 3 4 0 0 0`). -/
theorem musl_memcpy_ne_model (ctx' : Ctx) (bs bd : Nat) (ks kd : BlockKind) (m : Mem)
    (hs : m.blocks bs = some ⟨ks, true, .array (.int true 8) 7, .arr cexSrc⟩)
    (hd : m.blocks bd = some ⟨kd, true, .array (.int true 8) 7, .arr cexDst⟩) (hkd : kd ≠ .readonly)
    (hbs : bs < m.next) (hbd : bd < m.next) (hseg : m.next < 2 ^ 29) (hsd : bs ≠ bd) :
    evalCall ctx "musl_memcpy" [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 7] m ≠
      Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 7] m := by
  intro h
  rw [memcpy_model_cex ctx' bs bd ks kd m hs hd hkd hsd] at h
  exact musl_memcpy_cex_ub bs bd ks kd m hs hd hkd hbs hbd hseg hsd _ h

end EquivLean.Demo.Cir.Musl
