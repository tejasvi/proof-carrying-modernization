import Cobol
import EquivLean.Bridge.Cobol.Behaves
import EquivLean.Bridge.Cobol.Loops
import EquivLean.Bridge.Cobol.Corr
import EquivLean.Bridge.Aeneas.Behaves
import EquivLean.Bridge.Aeneas.Loops
import EquivLean.Demo.Gen.Aeneas.RecSum.Funs

/-!
# A cross-language product loop: RECSUM's `PERFORM … UNTIL` ≡ a Rust `while` loop

* **Source**: `examples/cobol/recsum/RECSUM.cob`, loaded with `cobol_program` from its surface
  IR.  The batch loop `PERFORM 2000-PROCESS UNTIL EOF` (read-ahead: the current record is in
  `IN-REC`, the body adds it to `WS-TOTAL`, writes `OUT-REC`, and reads the next record) runs
  as coblean's `Sem.loopUntil`; `EquivLean.Cobol.untilShape` / `untilTerminates` make it a
  `LoopShape` with fuel-based termination.
* **Target**: `examples/rust/recsum/src/lib.rs`, a `while i < recs.len()` loop over a slice of
  `(u32, i64)` records pushing `(id, running total)` to a `Vec`; its real Aeneas translation
  (`EquivLean/Demo/Gen/Aeneas/RecSum/Funs.lean`) is `loop recsum_loop.body`, a `LoopShape` by
  `EquivLean.Aeneas.loop_shape`.

`recsum_loop_sim` pairs the two loops **in lockstep** with `EquivLean.sim_loop_of_terminates`:
one COBOL iteration (test `EOF`, process one record) against one Rust iteration (test
`i < len`, process `recs[i]`), coupled by `Inv`.  Termination comes from the COBOL source (its
fuel), so no variant is needed.  The per-iteration obligations are one symbolic execution of
each side: coblean's `cobol_sym` for the COBOL iteration (`cobol_iter_cons`, `cobol_iter_nil`)
and the Aeneas `wp` lemmas for the Rust one (`rust_iter_cons`, `rust_iter_nil`).

Records: a Rust record `(id, amt)` is the COBOL input record `idBytes id ++ IN-AMT(amt)`
(`IN-AMT PIC S9(5)V99 COMP-3`, cents); an output `(id, total)` is the record
`idBytes id ++ OUT-TOTAL(total)` (`PIC S9(9)V99 COMP-3`).  As in coblean's
`Examples/RecSum.lean`, files of at most 9999 records keep `WS-TOTAL` in range.
-/

open Cobol
open Aeneas Aeneas.Std Result

cobol_program RecSumCob from "../../../examples/cobol/recsum/recsum.ir.json"

namespace EquivLean.Demo.RecSumAeneas

open RecSumCob
open EquivLean.Cobol (untilLoop untilStep untilBody withFuel IterRes IterExec)

/-- A Rust record: id and amount in cents. -/
abbrev RRec := U32 × I64

/-- The four bytes of `IN-ID` / `OUT-ID` for a Rust id (big-endian). -/
def idBytes (u : U32) : List UInt8 :=
  [UInt8.ofNat (u.val / 16777216), UInt8.ofNat (u.val / 65536), UInt8.ofNat (u.val / 256),
    UInt8.ofNat u.val]

@[simp] theorem length_idBytes (u : U32) : (idBytes u).length = 4 := rfl
@[simp] theorem take_idBytes (u : U32) : (idBytes u).take 4 = idBytes u := rfl
@[simp] theorem take_idBytes_append (u : U32) (l : List UInt8) :
    (idBytes u ++ l).take 4 = idBytes u := rfl
@[simp] theorem drop_idBytes_append (u : U32) (l : List UInt8) :
    (idBytes u ++ l).drop 4 = l := rfl
/-- Reading back an id just written (for symbolic execution). -/
theorem read_write_idBytes (m : Mem) (off : Nat) (u : U32) (hs : off + 4 ≤ m.size) :
    (m.write off (idBytes u)).read off 4 = idBytes u := Mem.read_write_same _ _ _ _ rfl hs

/-- The input record for a Rust record. -/
def encIn (r : RRec) : List UInt8 := idBytes r.1 ++ encodeNum {} IN_AMT.fmt r.2.val

/-- The output record with id `u` and total `v` (cents). -/
def encOut (u : U32) (v : Int) : List UInt8 := idBytes u ++ encodeNum {} OUT_TOTAL.fmt v

/-- The records written to `OUT-FILE` (file 2), oldest first. -/
def writesOf (evs : List Event) : List (List UInt8) :=
  evs.reverse.filterMap fun | .write 2 bs => some bs | _ => none

/-- The input file at the loop head when the records `rest` remain: the first of them is
already in `IN-REC`. -/
def inpOf : List RRec → List (Nat × List (List UInt8))
  | [] => [(1, [])]
  | _ :: xs => [(1, xs.map encIn)]

/-- The loop condition `EOF` (`WS-EOF = 'Y'`), as loaded. -/
abbrev eofCond : Cond :=
  .alnumCmp .eq (.ref ⟨11, ⟨18, 1, .alnum false⟩, [], none⟩) (.alnum [232])

/-- The loop body: one out-of-line `PERFORM` of paragraph `2000-PROCESS` (statement 1),
running paragraphs with fuel `N`. -/
abbrev body (N : Nat) : State → Sem.Res := Sem.performOnce (Sem.runFrom RecSumCob {} N) 1 2 (.para 2)

/-- The COBOL loop and its iteration, on loop states `(fuel, state)`. -/
abbrev cobLoop (N : Nat) := untilLoop false (Sem.condFn RecSumCob eofCond) (body N) Sem.noStep
abbrev cobStep (N : Nat) := untilStep false (Sem.condFn RecSumCob eofCond) (body N) Sem.noStep

/-- The Rust loop body on loop states `(out, total, i)`. -/
def rustBody (recs : Slice RRec) (s : alloc.vec.Vec RRec × I64 × Usize) :
    Result (ControlFlow (alloc.vec.Vec RRec × I64 × Usize) (alloc.vec.Vec RRec)) :=
  recsum.recsum_loop.body recs s.1 s.2.1 s.2.2

theorem recsum_loop_eq (recs : Slice RRec) (out : alloc.vec.Vec RRec) (total : I64) (i : Usize) :
    recsum.recsum_loop recs out total i = loop (rustBody recs) (out, total, i) := rfl

/-! ## The COBOL iteration -/

/-- COBOL state at the loop head with the records `rest` still to process, running total
`tot` and written records `ws`. -/
def CobInv (rest : List RRec) (tot : Int) (ws : List (List UInt8)) (st : State) : Prop :=
  ∃ mem saves outEv, st = ⟨mem, [], [], saves, [], outEv, inpOf rest, [], 0⟩ ∧ mem.size = 28 ∧
    (match rest with
     | [] => mem.field WS_EOF = [0xE8]
     | x :: _ => mem.field IN_ID = idBytes x.1 ∧
         decodeNum {} IN_AMT.fmt (mem.field IN_AMT) = some x.2.val ∧ mem.field WS_EOF = [0xD5]) ∧
    decodeNum {} WS_TOTAL.fmt (mem.field WS_TOTAL) = some tot ∧
    (∃ c, decodeNum {} WS_COUNT.fmt (mem.field WS_COUNT) = some c) ∧
    writesOf outEv = ws

/-- At end of file the COBOL loop leaves normally. -/
theorem cobol_iter_nil (N : Nat) {tot : Int} {ws : List (List UInt8)} {st : State}
    (h : CobInv [] tot ws st) :
    untilBody false (Sem.condFn RecSumCob eofCond) (body N) Sem.noStep st = .inl (.normal, st) := by
  obtain ⟨mem, saves, outEv, rfl, -, heof, -, -, -⟩ := h
  dsimp only at heof
  simp only [untilBody, eofCond]
  cobol_sym [heof]

/-- One COBOL iteration on a record `x`: add it to the total, write the output record, read
the next record. -/
theorem cobol_iter_cons (K : Nat) {x : RRec} {xs : List RRec} {tot : Int}
    {ws : List (List UInt8)} {st : State} (h : CobInv (x :: xs) tot ws st)
    (hx : x.2.val.natAbs < 10000000) (hxs : ∀ y ∈ xs, y.2.val.natAbs < 10000000)
    (htot : (tot + x.2.val).natAbs < 100000000000) :
    ∃ st', untilBody false (Sem.condFn RecSumCob eofCond) (body (K + 2)) Sem.noStep st = .inr st' ∧
      CobInv xs (tot + x.2.val) (ws ++ [encOut x.1 (tot + x.2.val)]) st' := by
  obtain ⟨mem, saves, outEv, rfl, hsize, ⟨hid, hamt, heof⟩, htotal, ⟨c, hcnt⟩, hwr⟩ := h
  have hbx : Cobol.InRange (-9999999) 9999999 x.2.val := by unfold Cobol.InRange; omega
  cases xs with
  | nil =>
    simp only [untilBody, eofCond, inpOf]
    cobol_sym [hsize, hid, hamt, heof, htotal, hcnt, encIn, List.length_append, length_encodeNum,
      length_idBytes, take_idBytes, List.take_left', List.drop_left']
    refine ⟨_, rfl, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · cobol_sym [hsize, length_idBytes, length_encodeNum, List.length_append]
    · cobol_sym [hsize, length_idBytes, length_encodeNum, List.length_append]
    · cobol_sym [hsize, length_idBytes, length_encodeNum, List.length_append]
    · refine ⟨(Sem.fitNum {} WS_COUNT.fmt (c + 1)).2, ?_⟩
      cobol_sym [hsize, length_idBytes, length_encodeNum, List.length_append]
    · unfold writesOf at hwr ⊢
      simp only [List.reverse_cons, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, encOut]
      rw [hwr]
      cobol_sym [hsize, length_idBytes, length_encodeNum, List.length_append, read_write_idBytes]
  | cons y ys =>
    have hy := hxs y (by simp)
    have hby : Cobol.InRange (-9999999) 9999999 y.2.val := by unfold Cobol.InRange; omega
    simp only [untilBody, eofCond, inpOf]
    cobol_sym [hsize, hid, hamt, heof, htotal, hcnt, encIn, List.length_append, length_encodeNum,
      length_idBytes, take_idBytes, List.take_left', List.drop_left', List.map_cons]
    refine ⟨_, rfl, _, _, _, rfl, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · cobol_sym [hsize, heof, length_idBytes, length_encodeNum, List.length_append]
    · cobol_sym [hsize, length_idBytes, length_encodeNum, List.length_append, take_idBytes_append]
    · cobol_sym [hsize, length_idBytes, length_encodeNum, List.length_append, drop_idBytes_append]
    · cobol_sym [hsize, heof, length_idBytes, length_encodeNum, List.length_append]
    · cobol_sym [hsize, heof, length_idBytes, length_encodeNum, List.length_append]
    · refine ⟨(Sem.fitNum {} WS_COUNT.fmt (c + 1)).2, ?_⟩
      cobol_sym [hsize, length_idBytes, length_encodeNum, List.length_append]
    · unfold writesOf at hwr ⊢
      simp only [List.reverse_cons, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, encOut]
      rw [hwr]
      cobol_sym [hsize, length_idBytes, length_encodeNum, List.length_append, read_write_idBytes]

/-! ## The Rust iteration -/

theorem wp_push {α : Type} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max)
    (Q : Except Error (alloc.vec.Vec α) → Prop)
    (hQ : ∀ v1 : alloc.vec.Vec α, v1.val = v.val ++ [x] → Q (.ok v1)) : wp (v.push x) Q :=
  EquivLean.Aeneas.wp_of_spec (alloc.vec.Vec.push_spec v x h) hQ

/-- At the end of the slice the Rust loop leaves with `out`. -/
theorem rust_iter_nil (recs : Slice RRec) (out : alloc.vec.Vec RRec) (total : I64) (i : Usize)
    (hdrop : recs.val.drop i.val = []) :
    wp (rustBody recs (out, total, i)) (fun ot => ot = .ok (.done out)) := by
  have hi : ¬ i < Slice.len recs := by
    rw [UScalar.lt_equiv, Slice.len_val]
    have := List.drop_eq_nil_iff.1 hdrop
    simp only [Slice.length]; omega
  simp only [rustBody, recsum.recsum_loop.body, hi, ↓reduceIte, EquivLean.Aeneas.wp_ok]

/-- One Rust iteration on the record `x = recs[i]`: no panic; continue with `(id, total + amt)`
pushed, the new total, and `i + 1`. -/
theorem rust_iter_cons (recs : Slice RRec) (out : alloc.vec.Vec RRec) (total : I64) (i : Usize)
    {x : RRec} {xs : List RRec} (hdrop : recs.val.drop i.val = x :: xs)
    (hlen : out.val.length = i.val)
    (hb : -9223372036854775808 ≤ total.val + x.2.val ∧ total.val + x.2.val ≤ 9223372036854775807) :
    wp (rustBody recs (out, total, i)) (fun ot => ∃ out' total' i',
      ot = .ok (.cont (out', total', i')) ∧ out'.val = out.val ++ [(x.1, total')] ∧
      total'.val = total.val + x.2.val ∧ i'.val = i.val + 1) := by
  have hi : i.val < recs.val.length := by
    have := congrArg List.length hdrop
    simp only [List.length_drop, List.length_cons] at this; omega
  have hx : recs.val[i.val] = x := by
    have := List.drop_eq_getElem_cons hi
    rw [hdrop] at this; exact (List.cons.inj this).1.symm
  have hlt : i < Slice.len recs := by
    rw [UScalar.lt_equiv, Slice.len_val]; exact hi
  have hmax := recs.property
  obtain ⟨xid, xamt⟩ := x
  have hcond : IScalar.min .I64 ≤ total.val + xamt.val ∧ total.val + xamt.val ≤ IScalar.max .I64 := by
    simp only [IScalar.min_def, IScalar.max_def, IScalarTy.numBits]; simp only at hb; omega
  have hpush : out.val.length < Usize.max := by omega
  have hone : (1#usize : Usize).val = 1 := by simp
  have hinc : i.val + (1#usize : Usize).val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq, hone]; omega
  simp only [rustBody, recsum.recsum_loop.body, hlt, ↓reduceIte, EquivLean.Aeneas.wp_bind,
    EquivLean.Aeneas.wp_Slice_index_usize, hi, ↓reduceDIte, hx, Aeneas.Std.uncurry_apply_pair,
    EquivLean.Aeneas.wp_IScalar_add_val, hcond, and_self]
  apply wp_push _ _ hpush
  intro v1 hv1
  simp only [EquivLean.Aeneas.wp_UScalar_add_val, hinc, ↓reduceDIte, EquivLean.Aeneas.wp_ok]
  exact ⟨_, _, _, rfl, hv1, IScalar.ofInt_val_eq _, by simp [hone]⟩

/-! ## The product loop -/

/-- The output records of a Rust output vector. -/
def outRecs (out : alloc.vec.Vec RRec) : List (List UInt8) := out.val.map fun r => encOut r.1 r.2.val

/-- **Coupling invariant** at the two loop heads: the Rust state `(out, total, i)` and the COBOL
state `(fuel, st)` have processed the same records `recs[0..i)`: the COBOL storage holds the
next record, the same running total and has written the records of `out`; the fuel covers the
records left. -/
def Inv (recs : Slice RRec) (s₁ : alloc.vec.Vec RRec × I64 × Usize) (s₂ : Nat × State) : Prop :=
  s₁.2.2.val ≤ recs.val.length ∧ recs.val.length - s₁.2.2.val < s₂.1 ∧
    s₁.1.val.length = s₁.2.2.val ∧ s₁.2.1.val.natAbs ≤ s₁.2.2.val * 9999999 ∧
    (∀ r ∈ s₁.1.val, r.2.val.natAbs < 100000000000) ∧
    CobInv (recs.val.drop s₁.2.2.val) s₁.2.1.val (outRecs s₁.1) s₂.2

/-- **Loop outcomes**: Rust returns `out` (no panic), COBOL leaves the loop normally at end of
file, having written the records of `out`. -/
def LoopRel : Except Error (alloc.vec.Vec RRec) → Signal × State → Prop
  | .ok out, (sig, st) => sig = .normal ∧ (∃ tot, CobInv [] tot (outRecs out) st) ∧
      ∀ r ∈ out.val, r.2.val.natAbs < 100000000000
  | .error _, _ => False

/-- **One product iteration**: a Rust iteration simulates the COBOL iteration, preserving the
coupling invariant (or both loops leave with related outcomes). -/
theorem step_sim (recs : Slice RRec) (K : Nat)
    (hrecs : ∀ r ∈ recs.val, r.2.val.natAbs < 10000000) (hlen : recs.val.length ≤ 9999) :
    ∀ s₁ s₂, Inv recs s₁ s₂ →
      Sim (StepRel EquivLean.Aeneas.loopCls id LoopRel (Inv recs)) (rustBody recs s₁)
        (cobStep (K + 2) s₂) := by
  rintro ⟨out, total, i⟩ ⟨fuel, st⟩ ⟨hi, hfuel, hout, hbnd, hob, hcob⟩
  simp only at hi hfuel hout hbnd hob hcob
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  show Sim _ _ (IterExec.mk (some (withFuel f
    (untilBody false (Sem.condFn RecSumCob eofCond) (body (K + 2)) Sem.noStep st))))
  rw [EquivLean.Cobol.sim_iterExec_some_iff]
  intro _
  cases hdrop : recs.val.drop i.val with
  | nil =>
    rw [hdrop] at hcob
    rw [cobol_iter_nil (K + 2) hcob]
    refine wp_mono (rust_iter_nil recs out total i hdrop) ?_
    rintro ot rfl
    simp only [stepRel_def, EquivLean.Aeneas.loopCls_done, withFuel, id]
    exact ⟨rfl, ⟨_, hcob⟩, hob⟩
  | cons x xs =>
    rw [hdrop] at hcob
    have hmem : ∀ y ∈ x :: xs, y ∈ recs.val := fun y hy => by
      rw [← hdrop] at hy; exact List.mem_of_mem_drop hy
    have hx := hrecs x (hmem x (by simp))
    have hxs : ∀ y ∈ xs, y.2.val.natAbs < 10000000 := fun y hy =>
      hrecs y (hmem y (List.mem_cons_of_mem _ hy))
    have hilt : i.val < recs.val.length := by
      have := congrArg List.length hdrop
      simp only [List.length_drop, List.length_cons] at this; omega
    have htot : (total.val + x.2.val).natAbs < 100000000000 := by omega
    obtain ⟨st', hst', hcob'⟩ := cobol_iter_cons K hcob hx hxs htot
    rw [hst']
    refine wp_mono (rust_iter_cons recs out total i hdrop hout (by omega)) ?_
    rintro ot ⟨out', total', i', rfl, hout', htot', hi'⟩
    simp only [stepRel_def, EquivLean.Aeneas.loopCls_cont, withFuel, id]
    have hd' : recs.val.drop i'.val = xs := by
      rw [hi', ← List.drop_drop, hdrop]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only; omega
    · simp only; omega
    · simp only [hout', List.length_append, List.length_cons, List.length_nil, hout, hi']
    · simp only [htot', hi']; omega
    · simp only [hout', List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (hr | rfl)
      · exact hob r hr
      · simp only [htot']; omega
    · simp only [hd', htot', outRecs, hout', List.map_append, List.map_cons, List.map_nil]
      exact hcob'

/-- **RECSUM's `PERFORM … UNTIL` loop ⊒ the Rust `while` loop**, by the lockstep product rule:
from coupled loop heads, the Aeneas loop simulates the COBOL loop.  No variant: the COBOL loop
terminates when safe (`untilTerminates`). -/
theorem recsum_loop_sim (recs : Slice RRec) (K : Nat)
    (hrecs : ∀ r ∈ recs.val, r.2.val.natAbs < 10000000) (hlen : recs.val.length ≤ 9999) :
    ∀ s₁ s₂, Inv recs s₁ s₂ → Sim LoopRel (loop (rustBody recs) s₁) (cobLoop (K + 2) s₂) :=
  sim_loop_of_terminates (EquivLean.Aeneas.loop_shape (rustBody recs))
    (EquivLean.Cobol.untilShape _ _ _ _) (EquivLean.Cobol.untilTerminates _ _ _ _) (Inv recs)
    (step_sim recs K hrecs hlen)

/-! ## The whole programs -/

/-- The COBOL loop alone ends normally (one-sided induction over the records left, with the
same per-iteration lemmas). -/
theorem cobol_loop_normal (K : Nat) : ∀ (rest : List RRec) (tot : Int) (ws : List (List UInt8))
    (fuel : Nat) (st : State), CobInv rest tot ws st → rest.length < fuel →
    (∀ y ∈ rest, y.2.val.natAbs < 10000000) → tot.natAbs + rest.length * 9999999 < 100000000000 →
    ∃ st', Sem.loopUntil false (Sem.condFn RecSumCob eofCond) (body (K + 2)) Sem.noStep fuel st =
      (.normal, st')
  | [], tot, ws, fuel, st, h, hf, _, _ => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    rw [EquivLean.Cobol.loopUntil_succ_eq, cobol_iter_nil (K + 2) h]
    exact ⟨st, rfl⟩
  | x :: xs, tot, ws, fuel, st, h, hf, hb, hbt => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hx := hb x (by simp)
    have hxs : ∀ y ∈ xs, y.2.val.natAbs < 10000000 := fun y hy => hb y (by simp [hy])
    simp only [List.length_cons] at hf hbt
    obtain ⟨st', hst', h'⟩ := cobol_iter_cons K h hx hxs (by omega)
    rw [EquivLean.Cobol.loopUntil_succ_eq, hst']
    exact cobol_loop_normal K xs _ _ f st' h' (by omega) hxs (by omega)

/-- The product loop from the initial states, combined with the COBOL loop's result: the Rust
loop returns (no panic) the output vector whose records COBOL has written. -/
theorem loop_combined (recs : Slice RRec) (K : Nat)
    (hrecs : ∀ r ∈ recs.val, r.2.val.natAbs < 10000000) (hlen : recs.val.length ≤ 9999)
    (fuel : Nat) (st : State) (h0 : CobInv recs.val 0 [] st) (hf : recs.val.length < fuel) :
    ∃ st', Sem.loopUntil false (Sem.condFn RecSumCob eofCond) (body (K + 2)) Sem.noStep fuel st =
        (.normal, st') ∧
      wp (loop (rustBody recs) (alloc.vec.Vec.new RRec, 0#i64, 0#usize))
        (fun ot => ∃ out, ot = .ok out ∧ writesOf st'.out = outRecs out ∧
          ∀ r ∈ out.val, r.2.val.natAbs < 100000000000) := by
  obtain ⟨st', heq⟩ := cobol_loop_normal K recs.val 0 [] fuel st h0 hf hrecs (by simp; omega)
  refine ⟨st', heq, ?_⟩
  have hI : Inv recs (alloc.vec.Vec.new RRec, 0#i64, 0#usize) (fuel, st) := by
    refine ⟨by simp, by simp; omega, by simp, by simp, by simp, ?_⟩
    simp only [IScalar.ofInt_val_eq]
    have hv : outRecs (alloc.vec.Vec.new RRec) = [] := by simp [outRecs]
    simpa [hv] using h0
  have hsim := recsum_loop_sim recs K hrecs hlen _ _ hI
  have hok : EquivLean.Cobol.Ok (.normal, st') := rfl
  have hsafe : Safe (cobLoop (K + 2) (fuel, st)) := by
    show EquivLean.Cobol.Ok (Sem.loopUntil _ _ _ _ fuel st); rw [heq]; exact hok
  have hrun : Runs (cobLoop (K + 2) (fuel, st)) (.normal, st') :=
    ⟨by show _ = Sem.loopUntil _ _ _ _ fuel st; rw [heq], hsafe⟩
  rw [sim_iff_of_runs hsafe hrun] at hsim
  refine wp_mono hsim fun ot hrel => ?_
  cases ot with
  | error e => exact hrel.elim
  | ok out =>
    obtain ⟨-, ⟨tot, mem, saves, outEv, hst, -, -, -, -, hw⟩, hb⟩ := hrel
    exact ⟨out, rfl, by rw [hst]; exact hw, hb⟩

open Lean Meta Elab Tactic in
/-- `name_loop_state s hs`: in a goal containing a folded `PERFORM … UNTIL` loop
`Sem.loopUntil ta c b step fuel st`, replace the state `st` by a new variable `s` with
`hs : st = s`. -/
elab "name_loop_state " s:ident hs:ident : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let some loop := ty.find? (fun t => t.isAppOfArity ``Sem.loopUntil 6)
    | throwError "name_loop_state: no `Sem.loopUntil` in the goal"
  let stTerm ← Term.exprToSyntax (loop.getArg! 5)
  evalTactic (← `(tactic| generalize $hs:ident : $stTerm = $s:ident))

/-- A Rust output record `(id, total)` and a COBOL output record: the same id bytes, and an
`OUT-TOTAL` field holding the decimal `scaled 2 total` (shared `Decimal` model). -/
def OutCorr (r : RRec) (bs : List UInt8) : Prop :=
  bs.take 4 = idBytes r.1 ∧
    EquivLean.Cobol.fieldDec {} OUT_TOTAL.fmt (bs.drop 4) = some (EquivLean.Cobol.scaled 2 r.2.val)

/-- Whole-program outcomes: Rust returns `out` (no panic), COBOL ends with `GOBACK`, and the
records written to `OUT-FILE` correspond one to one to `out` (`OutCorr`, through `Decimal`). -/
def ProgRel : Except Error (alloc.vec.Vec RRec) → Signal × State → Prop
  | .ok out, (sig, st) => sig = .stop .goback ∧ ListRel OutCorr out.val (writesOf st.out)
  | .error _, _ => False

theorem outCorr_encOut (r : RRec) (h : r.2.val.natAbs < 100000000000) :
    OutCorr r (encOut r.1 r.2.val) := by
  refine ⟨take_idBytes_append _ _, ?_⟩
  rw [encOut, drop_idBytes_append]
  exact EquivLean.Cobol.fieldDec_encodeNum {} OUT_TOTAL.fmt r.2.val (by decide) (by decide)
    (by simp [NumFmt.Holds, NumFmt.fullBinary]; omega)

theorem listRel_outRecs (out : alloc.vec.Vec RRec)
    (h : ∀ r ∈ out.val, r.2.val.natAbs < 100000000000) : ListRel OutCorr out.val (outRecs out) := by
  unfold outRecs
  generalize out.val = l at h ⊢
  induction l with
  | nil => exact .nil
  | cons r l ih =>
    exact .cons (outCorr_encOut r (h r (by simp))) (ih fun r' hr' => h r' (by simp [hr']))

/-- **Both whole programs, one proof.**  For every input file of at most 9999 records and enough
fuel, the COBOL program ends with `GOBACK` (a safe run), and the Rust function returns (no
panic) a vector whose records are exactly what the COBOL program writes to `OUT-FILE`.  The
proof runs both programs to their loops (coblean's symbolic executor; `name_loop_state` names
the COBOL state at the loop head), pairs the loops with the lockstep product rule
(`recsum_loop_sim` via `loop_combined`), and runs the COBOL suffix (`GOBACK`). -/
theorem recsum_ok_wp (m : Mem) (hm : m.size = 28) (recs : Slice RRec) (n : Nat)
    (hrecs : ∀ r ∈ recs.val, r.2.val.natAbs < 10000000) (hlen : recs.val.length ≤ 9999)
    (hn : recs.val.length < n) :
    EquivLean.Cobol.Ok (RecSumCob.run {} (n + 10) (RecSumCob.initState m [(1, recs.val.map encIn)])) ∧
      wp (recsum.recsum recs) (fun ot =>
        ProgRel ot (RecSumCob.run {} (n + 10) (RecSumCob.initState m [(1, recs.val.map encIn)]))) := by
  have hloop := loop_combined recs (n + 7) hrecs hlen
  rw [show recsum.recsum recs = loop (rustBody recs) (alloc.vec.Vec.new RRec, 0#i64, 0#usize) from rfl]
  cases hrv : recs.val with
  | nil =>
    simp only [List.map_nil]
    cobol_sym [hm]
    name_loop_state st0 hst0
    have h0 : CobInv recs.val 0 [] st0 := by
      rw [hrv, ← hst0]
      refine ⟨_, _, _, rfl, ?_, ?_, ?_, ⟨0, ?_⟩, rfl⟩ <;> cobol_sym [hm]
    obtain ⟨st', heq, hwp⟩ := hloop (n + 9) st0 h0 (by rw [hrv]; simp)
    rw [heq]
    cobol_sym
    exact wp_mono hwp fun ot ⟨out, hout, hw, hb⟩ => by
      subst hout; exact ⟨rfl, hw ▸ listRel_outRecs out hb⟩
  | cons x xs =>
    have hx := hrecs x (by rw [hrv]; simp)
    have hbx : Cobol.InRange (-9999999) 9999999 x.2.val := by unfold Cobol.InRange; omega
    simp only [List.map_cons]
    cobol_sym [hm, encIn, List.length_append, length_encodeNum, length_idBytes]
    name_loop_state st0 hst0
    have h0 : CobInv recs.val 0 [] st0 := by
      rw [hrv, ← hst0]
      refine ⟨_, _, _, rfl, ?_, ⟨?_, ?_, ?_⟩, ?_, ⟨0, ?_⟩, rfl⟩ <;>
        cobol_sym [hm, length_idBytes, length_encodeNum, List.length_append, take_idBytes_append,
          drop_idBytes_append]
    obtain ⟨st', heq, hwp⟩ := hloop (n + 9) st0 h0 (by omega)
    rw [heq]
    cobol_sym
    exact wp_mono hwp fun ot ⟨out, hout, hw, hb⟩ => by
      subst hout; exact ⟨rfl, hw ▸ listRel_outRecs out hb⟩

/-- **RECSUM ⊑ recsum.rs (Aeneas).** -/
theorem recsum_sim (m : Mem) (hm : m.size = 28) (recs : Slice RRec) (n : Nat)
    (hrecs : ∀ r ∈ recs.val, r.2.val.natAbs < 10000000) (hlen : recs.val.length ≤ 9999)
    (hn : recs.val.length < n) :
    Sim ProgRel (recsum.recsum recs)
      (EquivLean.Cobol.run RecSumCob {} (n + 10) (RecSumCob.initState m [(1, recs.val.map encIn)])) := by
  rw [EquivLean.Cobol.run, EquivLean.Cobol.sim_exec_iff]
  exact fun _ => (recsum_ok_wp m hm recs n hrecs hlen hn).2

/-- **RECSUM ≈ recsum.rs (Aeneas)**: simulation in both directions. -/
theorem recsum_equiv (m : Mem) (hm : m.size = 28) (recs : Slice RRec) (n : Nat)
    (hrecs : ∀ r ∈ recs.val, r.2.val.natAbs < 10000000) (hlen : recs.val.length ≤ 9999)
    (hn : recs.val.length < n) :
    Equiv ProgRel (recsum.recsum recs)
      (EquivLean.Cobol.run RecSumCob {} (n + 10) (RecSumCob.initState m [(1, recs.val.map encIn)])) := by
  obtain ⟨hok, hw⟩ := recsum_ok_wp m hm recs n hrecs hlen hn
  have hsim := recsum_sim m hm recs n hrecs hlen hn
  obtain ⟨ot, hot, hrel⟩ := wp_exists hw
  rw [EquivLean.Cobol.run] at hsim ⊢
  refine ⟨hsim, fun _ => ?_⟩
  rw [EquivLean.Cobol.safe_exec_iff]
  refine ⟨hok, fun os hos => ⟨ot, hot, ?_⟩⟩
  obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
  rw [h1]
  exact hrel

/-- **The Rust code does not panic (and terminates) on any valid input file.** -/
theorem recsum_rust_no_panic (m : Mem) (hm : m.size = 28) (recs : Slice RRec) (n : Nat)
    (hrecs : ∀ r ∈ recs.val, r.2.val.natAbs < 10000000) (hlen : recs.val.length ≤ 9999)
    (hn : recs.val.length < n) :
    wp (recsum.recsum recs) (fun ot => ∃ out, ot = .ok out) :=
  wp_mono (recsum_ok_wp m hm recs n hrecs hlen hn).2 fun ot hrel => by
    cases ot with
    | ok out => exact ⟨out, rfl⟩
    | error e => exact hrel.elim

end EquivLean.Demo.RecSumAeneas

#print axioms EquivLean.Demo.RecSumAeneas.recsum_loop_sim
#print axioms EquivLean.Demo.RecSumAeneas.recsum_ok_wp
#print axioms EquivLean.Demo.RecSumAeneas.recsum_sim
#print axioms EquivLean.Demo.RecSumAeneas.recsum_equiv
#print axioms EquivLean.Demo.RecSumAeneas.recsum_rust_no_panic
