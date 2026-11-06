import EquivLean.Modernize.Cbstm03a.Java.Run2.Steps2

/-! # CBSTM03A → Java `run`, the load loop: statements 80–87 (the record's three fields cut, `saveCard` compared;
the same card: `trCnt` counted, to 92; a new card: to 88) -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space GrowsK Kept keeps_trans grows_split
  fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

/-- The loop head's facts the statements after the comparison read. -/
def HeadAt (p : LP) : Prop :=
  p.fr.get 11 = some (.ref p.t1) ∧ p.σ.heap p.t1 = some (.array (.cls "java.lang.String") p.xs) ∧
    p.fr.get 16 = some (.ref p.mem) ∧ p.fr.get 24 = some (.ref p.trct) ∧ p.fr.get 1 = some (.ref p.st1) ∧
    p.σ.heap p.st1 = some (.array (.prim .int) [.int (BitVec.ofNat 32 (p.k + 1)), .int 0]) ∧
    p.σ.heap p.y = some (.str p.ty) ∧ (∃ vsm, p.σ.heap p.mem = some (.array (.cls "java.lang.String") vsm)) ∧
    SlotsAt p.σ p.mem p.s.m ∧ p.σ.heap p.trct = some (.array (.prim .long) p.s.trct) ∧ p.s.trct.length = 51

attribute [-jsimp] List.take_succ
attribute [local irreducible] SlotsAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem seg1N (g : RunG) (args : List Value) (σ0 : State) (p : LP)
    (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1)
    (hI0 : p.σ.initOf "Cbstm03a" = .done) (x33 x32 : Addr)
    (h33 : p.fr.get 33 = some (.ref x33)) (hx33 : p.σ.heap x33 = some (.str p.r)) (hrl : p.r.length = 350)
    (h32 : p.fr.get 32 = some (.ref x32)) (hx32 : p.σ.heap x32 = some (.str p.s.save))
    (h18 : p.fr.get 18 = some (.long p.s.cr)) (h17 : p.fr.get 17 = some (.long p.s.tr))
    (hsv : ¬ List.take 16 p.r = p.s.save) (hsv' : ¬ p.s.save = List.take 16 p.r) (hc : Kept (HeadAt p)) :
    segWP g args σ0 (cuts88 g args σ0 p) 40 80 p.fr p.σ := by
  unfold segWP
  jvc [runCallees, cuts88, cuts92, cuts95, cuts98, cuts100, cuts113, cuts0, runInv, runSpecG, trnxTextSig,
    xrefTextSig, custTextSig, acctTextSig, spacesSig, fixSig, repeatSig, seqReadSig, setTrctSig, getTrctSig,
    cardOffSig, tranOffSig, memWriteSig, memReadSig, abendSig, createStatementSig, writeTransSig, stmtSig,
    htmlSig, ebcCompareSig, decodeZonedSig, trunc11Sig, fmtZSig, ite_nat_ne]
  all_goals
    obtain ⟨h11, ht1, h16, h24, h1, hst1, hy, ⟨vsm, hmem⟩, hsl, htr, htl⟩ := Kept.elim hc
    unfold A88 MidBase FrameK RecLocs TabAt
    exact ⟨⟨Kept.intro ⟨keeps_mono (A := fun _ => False) (by keeps_peel) (fun _ h => h.elim), rfl, rfl,
        sameLocs_step (fun _ _ => rfl)
          (fun i a b _ _ _ _ _ _ _ j l => by simp only [Frame.get_setLocal, a, b, j, l, if_false])⟩,
      hI0, by simp [Frame.get_setLocal, h11], heap_keeps' (A := fun _ => False) (by keeps_peel) ht1 id,
      by simp [Frame.get_setLocal, h16], by simp [Frame.get_setLocal, h24], by simp [Frame.get_setLocal, h1],
      heap_keeps' (A := fun _ => False) (by keeps_peel) hst1 id,
      heap_keeps' (A := fun _ => False) (by keeps_peel) hy id,
      vsm, heap_keeps' (A := fun _ => False) (by keeps_peel) hmem id⟩,
      ⟨p.σ.next, p.σ.next + 1, p.σ.next + 1 + 1, by simp [Frame.get_setLocal], by simp [State.heap_alloc, State.next_alloc, sub]; try exact fun h => absurd h (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self _))),
        by simp [Frame.get_setLocal], by simp [State.heap_alloc, State.next_alloc, sub],
        by simp [Frame.get_setLocal], by simp [State.heap_alloc, State.next_alloc, sub, List.take_of_length_le, hrl]⟩,
      ⟨slotsAt_keeps (A := fun _ => False) (by keeps_peel) (fun _ h => h.elim) hsl id,
        heap_keeps' (A := fun _ => False) (by keeps_peel) htr id,
        by simp [Frame.get_setLocal, h18], by simp [Frame.get_setLocal, h17]⟩, htl⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem seg1E (g : RunG) (args : List Value) (σ0 : State) (p : LP)
    (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1)
    (hI0 : p.σ.initOf "Cbstm03a" = .done) (x33 x32 : Addr)
    (h33 : p.fr.get 33 = some (.ref x33)) (hx33 : p.σ.heap x33 = some (.str p.r)) (hrl : p.r.length = 350)
    (h32 : p.fr.get 32 = some (.ref x32)) (hx32 : p.σ.heap x32 = some (.str p.s.save))
    (h18 : p.fr.get 18 = some (.long p.s.cr)) (h17 : p.fr.get 17 = some (.long p.s.tr))
    (hsv : List.take 16 p.r = p.s.save) (hc : Kept (HeadAt p)) :
    segWP g args σ0 (cuts92 g args σ0 p) 40 80 p.fr p.σ := by
  unfold segWP
  jvc [runCallees, cuts92, cuts95, cuts98, cuts100, cuts113, cuts0, runInv, runSpecG, trnxTextSig,
    xrefTextSig, custTextSig, acctTextSig, spacesSig, fixSig, repeatSig, seqReadSig, setTrctSig, getTrctSig,
    cardOffSig, tranOffSig, memWriteSig, memReadSig, abendSig, createStatementSig, writeTransSig, stmtSig,
    htmlSig, ebcCompareSig, decodeZonedSig, trunc11Sig, fmtZSig, ite_nat_ne]
  all_goals
    obtain ⟨h11, ht1, h16, h24, h1, hst1, hy, ⟨vsm, hmem⟩, hsl, htr, htl⟩ := Kept.elim hc
    have hsame : p.s.save = sub p.r 0 16 := by simp only [sub, List.drop_zero]; exact hsv.symm
    obtain ⟨c1, c2, c3⟩ := ldStep_same_cr hsame
    unfold A92 MidBase FrameK RecLocs TabAt
    exact ⟨⟨Kept.intro ⟨keeps_mono (A := fun _ => False) (by keeps_peel) (fun _ h => h.elim), rfl, rfl,
        sameLocs_step (fun _ _ => rfl)
          (fun i a b _ _ _ _ _ h' _ j l => by simp only [Frame.get_setLocal, a, b, h', j, l, if_false])⟩,
      hI0, by simp [Frame.get_setLocal, h11], heap_keeps' (A := fun _ => False) (by keeps_peel) ht1 id,
      by simp [Frame.get_setLocal, h16], by simp [Frame.get_setLocal, h24], by simp [Frame.get_setLocal, h1],
      heap_keeps' (A := fun _ => False) (by keeps_peel) hst1 id,
      heap_keeps' (A := fun _ => False) (by keeps_peel) hy id,
      vsm, heap_keeps' (A := fun _ => False) (by keeps_peel) hmem id⟩,
      ⟨p.σ.next, p.σ.next + 1, p.σ.next + 1 + 1, by simp [Frame.get_setLocal], by simp [State.heap_alloc, State.next_alloc, hsame]; try exact fun h => absurd h (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self _))),
        by simp [Frame.get_setLocal], by simp [State.heap_alloc, State.next_alloc, sub],
        by simp [Frame.get_setLocal], by simp [State.heap_alloc, State.next_alloc, sub, List.take_of_length_le, hrl]⟩,
      slotsAt_keeps (A := fun _ => False) (by keeps_peel) (fun _ h => h.elim) hsl id,
      by rw [c3]; exact heap_keeps' (A := fun _ => False) (by keeps_peel) htr id,
      by rw [c1]; simp [Frame.get_setLocal, h18], by rw [c2]; simp [Frame.get_setLocal]⟩

end EquivLean.Modernize.Cbstm03a.Java.Seg2

#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg2.seg1N
#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg2.seg1E
