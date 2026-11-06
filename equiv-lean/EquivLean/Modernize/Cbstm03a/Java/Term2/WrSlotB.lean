import EquivLean.Modernize.Cbstm03a.Java.Term2.WrSlot
import EquivLean.Modernize.Cbstm03a.Java.Term2.SlotLem

/-!
# CBSTM03A → Java, termination: `memWrite`'s slot step from statement 26

The slot `slots[idx]`: out of bounds (an exception), `null` (replaced by `spaces(len)`) or a string; then the
update `slots[idx] = cur` and `pos += take`. The slots stay `null` or strings (`slotOk_step`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem wr_tslot26n (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (v : Nat) (idx len within take : I32)
    (ha : args = [.ref a, .long off, .ref x])
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h5 : fr.get 5 = some (.int n))
    (h6 : fr.get 6 = some (.int idx)) (h7 : fr.get 7 = some (.int len)) (h8 : fr.get 8 = some (.int within))
    (h10 : fr.get 10 = some (.int pos)) (h11 : fr.get 11 = some (.int take)) (h12 : fr.get 12 = some (.ref x))
    (hx : σ.heap x = some (.str t)) (hav : σ.heap a = some (.array (.cls "java.lang.String") vs))
    (hok : SlotOk σ vs) (hoff0 : -2147483648 < off.toInt) (hoff1 : off.toInt < 171156) (hp0 : 0 ≤ pos.toInt)
    (htk1 : 1 ≤ take.toInt) (htk2 : take.toInt ≤ n.toInt - pos.toInt) (hlen : len.toInt ≤ 1073741824)
    (hinit : σ.initOf "Cbstm03a" = .done) (hv : v = (2147483648 - pos.toInt).toNat)
    (hb0 : 0 ≤ idx.toInt) (hb1 : idx.toInt < vs.length) (hb : (BitVec.toInt idx).toNat < vs.length)
    (hnull : vs[(BitVec.toInt idx).toNat] = Value.null) :
    wrTWP [(5, fun fr σ => wrInv args σ0 fr σ ∧ wrVar args σ0 fr σ < v)] 20 26 fr σ := by
  subst ha hv
  unfold wrTWP
  jvc [wrTerm, wrInv, WrAt, wrVar, memCallees, spacesSig, spacesSpecI]
  all_goals
    refine slotOk_step hok hav ?_ ?_ ?_
    · repeat (first | exact strKeep_refl _ | refine strKeep_alloc ?_ _ | exact strKeep_of_frame ‹_›)
    · simp only [State.next_alloc]; exact lt_add4 (State.lt_next_of_heap hav) ‹_›
    · simp only [State.next_alloc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem wr_tslot26s (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (v : Nat) (idx len within take : I32)
    (ha : args = [.ref a, .long off, .ref x])
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h5 : fr.get 5 = some (.int n))
    (h6 : fr.get 6 = some (.int idx)) (h7 : fr.get 7 = some (.int len)) (h8 : fr.get 8 = some (.int within))
    (h10 : fr.get 10 = some (.int pos)) (h11 : fr.get 11 = some (.int take)) (h12 : fr.get 12 = some (.ref x))
    (hx : σ.heap x = some (.str t)) (hav : σ.heap a = some (.array (.cls "java.lang.String") vs))
    (hok : SlotOk σ vs) (hoff0 : -2147483648 < off.toInt) (hoff1 : off.toInt < 171156) (hp0 : 0 ≤ pos.toInt)
    (htk1 : 1 ≤ take.toInt) (htk2 : take.toInt ≤ n.toInt - pos.toInt) (hlen : len.toInt ≤ 1073741824)
    (hinit : σ.initOf "Cbstm03a" = .done) (hv : v = (2147483648 - pos.toInt).toNat)
    (hb0 : 0 ≤ idx.toInt) (hb1 : idx.toInt < vs.length) (hb : (BitVec.toInt idx).toNat < vs.length)
    (y : Addr) (s : JStr) (hy : vs[(BitVec.toInt idx).toNat] = Value.ref y) (hys : σ.heap y = some (.str s)) :
    wrTWP [(5, fun fr σ => wrInv args σ0 fr σ ∧ wrVar args σ0 fr σ < v)] 20 26 fr σ := by
  subst ha hv
  unfold wrTWP
  jvc [wrTerm, wrInv, WrAt, wrVar, memCallees, spacesSig, spacesSpecI]
  all_goals
    refine slotOk_step hok hav ?_ ?_ ?_
    · repeat (first | exact strKeep_refl _ | refine strKeep_alloc ?_ _ | exact strKeep_of_frame ‹_›)
    · simp only [State.next_alloc]; exact lt_add4 (State.lt_next_of_heap hav) (Nat.le_refl _)
    · simp only [State.next_alloc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem wr_tslot26o (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (v : Nat) (idx len within take : I32)
    (h0 : fr.get 0 = some (.ref a)) (h6 : fr.get 6 = some (.int idx))
    (hav : σ.heap a = some (.array (.cls "java.lang.String") vs))
    (hb : ¬(0 ≤ idx.toInt ∧ idx.toInt < vs.length)) :
    wrTWP [(5, fun fr σ => wrInv args σ0 fr σ ∧ wrVar args σ0 fr σ < v)] 20 26 fr σ := by
  unfold wrTWP
  jvc [wrTerm, wrInv, WrAt, wrVar, memCallees, spacesSig, spacesSpecI]

end EquivLean.Modernize.Cbstm03a.Java.Term2
