import EquivLean.Modernize.Cbstm03a.Java.Term2.MemRead

/-!
# CBSTM03A → Java, termination: `memRead`'s slot step

Extra cut points at statement 28 (`slotIndex(o)`: the offset `o` as a variable) and 37 (`cur = slots[skip]`: the
step `take` as a variable with `1 ≤ take ≤ n - pos`); from 37: the slot out of bounds, `null` or a string.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

/-- At statement 28: the offset `o = off + pos` in `[0, MEM_SZ)`. -/
def RdO (a : Addr) (off : I64) (sb : Addr) (b : JStr) (vs : List Value) (n pos : I32) (fr : Frame) (σ : State) :
    Prop :=
  ∃ o : I64, fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 2 = some (.long o) ∧
    fr.get 5 = some (.int n) ∧ fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" b) ∧
    σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ SlotOk σ vs ∧
    -2147483648 < off.toInt ∧ off.toInt < 171156 ∧ 0 ≤ pos.toInt ∧ pos.toInt < n.toInt ∧
    n.toInt ≤ 1073741824 ∧ 0 ≤ o.toInt ∧ o.toInt < 171156 ∧ σ.initOf "Cbstm03a" = .done

/-- At statement 37: the step `take`, `1 ≤ take ≤ n - pos`. -/
def RdTk (a : Addr) (off : I64) (sb : Addr) (b : JStr) (vs : List Value) (n pos : I32) (fr : Frame)
    (σ : State) : Prop :=
  ∃ idx len within take : I32, fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧
    fr.get 5 = some (.int n) ∧ fr.get 6 = some (.int within) ∧ fr.get 7 = some (.int len) ∧
    fr.get 9 = some (.int idx) ∧ fr.get 10 = some (.int pos) ∧ fr.get 11 = some (.int take) ∧
    fr.get 12 = some (.ref sb) ∧ σ.heap sb = some (.builder "java.lang.StringBuilder" b) ∧
    σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ SlotOk σ vs ∧
    -2147483648 < off.toInt ∧ off.toInt < 171156 ∧ 0 ≤ pos.toInt ∧ 1 ≤ take.toInt ∧
    take.toInt ≤ n.toInt - pos.toInt ∧ n.toInt ≤ 1073741824 ∧ σ.initOf "Cbstm03a" = .done

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
/-- Statements 6 … 28 of a slot step. -/
theorem rd_tslot6 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr)
    (b : JStr) (vs : List Value) (n pos : I32) (v : Nat)
    (h : RdAt fr σ a off sb b vs n pos) (hx : pos.toInt < n.toInt)
    (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt) (h0 : 0 ≤ off.toInt + pos.toInt)
    (h1 : off.toInt + pos.toInt < 171156) :
    rdTWP ((28, RdO a off sb b vs n pos) ::
      [(6, fun fr σ => rdInv args σ0 fr σ ∧ rdVar args σ0 fr σ < v)]) 20 6 fr σ := by
  unfold rdTWP
  jvc [rdTerm, rdInv, RdAt, rdVar, rdCallees, RdO]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
/-- Statements 28 … 37: the slot helpers. -/
theorem rd_tslot28 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr)
    (b : JStr) (vs : List Value) (n pos : I32) (v : Nat) (o : I64) (k : Nat) (i l w : I32) (s : I64)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h2 : fr.get 2 = some (.long o))
    (h5 : fr.get 5 = some (.int n)) (h10 : fr.get 10 = some (.int pos)) (h12 : fr.get 12 = some (.ref sb))
    (hsb : σ.heap sb = some (.builder "java.lang.StringBuilder" b))
    (hav : σ.heap a = some (.array (.cls "java.lang.String") vs))
    (hok : SlotOk σ vs) (hoff0 : -2147483648 < off.toInt) (hoff1 : off.toInt < 171156) (hp0 : 0 ≤ pos.toInt)
    (hpn : pos.toInt < n.toInt) (hn : n.toInt ≤ 1073741824) (ho0 : 0 ≤ o.toInt) (ho1 : o.toInt < 171156)
    (hinit : σ.initOf "Cbstm03a" = .done)
    (hk : slotIdx o.toNat = k) (hi : BitVec.ofNat 32 k = i) (hl : BitVec.ofNat 32 (slotLn i.toNat) = l)
    (hs : BitVec.ofNat 64 (slotSt i.toNat) = s) (hw : JLong.toInt (o - s) = w)
    (hit : i.toInt = k) (hk1 : k < 561) (hl1 : 16 ≤ l.toInt) (hl2 : l.toInt ≤ 334) (hw0 : 0 ≤ w.toInt)
    (hwl : w.toInt < l.toInt) :
    rdTWP ((37, RdTk a off sb b vs n pos) ::
      [(6, fun fr σ => rdInv args σ0 fr σ ∧ rdVar args σ0 fr σ < v)]) 20 28 fr σ := by
  unfold rdTWP
  jvc [rdTerm, rdInv, RdAt, rdVar, rdCallees, RdTk, slotIndexSig, slotIndexSpec, slotLenSig, slotLenSpec,
    slotStartSig, slotStartSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem rd_tslot37n (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr)
    (b : JStr) (vs : List Value) (n pos : I32) (v : Nat) (idx len within take : I32)
    (ha : args = [.ref a, .long off, .int n])
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h5 : fr.get 5 = some (.int n))
    (h6 : fr.get 6 = some (.int within)) (h7 : fr.get 7 = some (.int len)) (h9 : fr.get 9 = some (.int idx))
    (h10 : fr.get 10 = some (.int pos)) (h11 : fr.get 11 = some (.int take)) (h12 : fr.get 12 = some (.ref sb))
    (hsb : σ.heap sb = some (.builder "java.lang.StringBuilder" b))
    (hav : σ.heap a = some (.array (.cls "java.lang.String") vs))
    (hok : SlotOk σ vs) (hoff0 : -2147483648 < off.toInt) (hoff1 : off.toInt < 171156) (hp0 : 0 ≤ pos.toInt)
    (htk1 : 1 ≤ take.toInt) (htk2 : take.toInt ≤ n.toInt - pos.toInt) (hn : n.toInt ≤ 1073741824)
    (hinit : σ.initOf "Cbstm03a" = .done) (hv : v = (2147483648 - pos.toInt).toNat)
    (hb0 : 0 ≤ idx.toInt) (hb1 : idx.toInt < vs.length) (hb : (BitVec.toInt idx).toNat < vs.length)
    (hnull : vs[(BitVec.toInt idx).toNat] = Value.null) :
    rdTWP [(6, fun fr σ => rdInv args σ0 fr σ ∧ rdVar args σ0 fr σ < v)] 20 37 fr σ := by
  subst ha hv
  unfold rdTWP
  jvc [rdTerm, rdInv, RdAt, rdVar, rdCallees, spacesSig, spacesSpecI]
  all_goals
    refine slotOk_keep hok ?_
    repeat (first | exact strKeep_refl _ | refine strKeep_alloc ?_ _ |
      refine strKeep_setObj ?_ (fun s e => by rw [hsb] at e; cases e) _ | exact strKeep_of_frame ‹_›)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem rd_tslot37s (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr)
    (b : JStr) (vs : List Value) (n pos : I32) (v : Nat) (idx len within take : I32)
    (ha : args = [.ref a, .long off, .int n])
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h5 : fr.get 5 = some (.int n))
    (h6 : fr.get 6 = some (.int within)) (h7 : fr.get 7 = some (.int len)) (h9 : fr.get 9 = some (.int idx))
    (h10 : fr.get 10 = some (.int pos)) (h11 : fr.get 11 = some (.int take)) (h12 : fr.get 12 = some (.ref sb))
    (hsb : σ.heap sb = some (.builder "java.lang.StringBuilder" b))
    (hav : σ.heap a = some (.array (.cls "java.lang.String") vs))
    (hok : SlotOk σ vs) (hoff0 : -2147483648 < off.toInt) (hoff1 : off.toInt < 171156) (hp0 : 0 ≤ pos.toInt)
    (htk1 : 1 ≤ take.toInt) (htk2 : take.toInt ≤ n.toInt - pos.toInt) (hn : n.toInt ≤ 1073741824)
    (hinit : σ.initOf "Cbstm03a" = .done) (hv : v = (2147483648 - pos.toInt).toNat)
    (hb0 : 0 ≤ idx.toInt) (hb1 : idx.toInt < vs.length) (hb : (BitVec.toInt idx).toNat < vs.length)
    (y : Addr) (s : JStr) (hy : vs[(BitVec.toInt idx).toNat] = Value.ref y) (hys : σ.heap y = some (.str s)) :
    rdTWP [(6, fun fr σ => rdInv args σ0 fr σ ∧ rdVar args σ0 fr σ < v)] 20 37 fr σ := by
  subst ha hv
  unfold rdTWP
  jvc [rdTerm, rdInv, RdAt, rdVar, rdCallees, spacesSig, spacesSpecI]
  all_goals
    refine slotOk_keep hok ?_
    repeat (first | exact strKeep_refl _ | refine strKeep_alloc ?_ _ |
      refine strKeep_setObj ?_ (fun s e => by rw [hsb] at e; cases e) _ | exact strKeep_of_frame ‹_›)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem rd_tslot37o (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (vs : List Value)
    (v : Nat) (idx : I32) (h0 : fr.get 0 = some (.ref a)) (h9 : fr.get 9 = some (.int idx))
    (hav : σ.heap a = some (.array (.cls "java.lang.String") vs))
    (hb : ¬(0 ≤ idx.toInt ∧ idx.toInt < vs.length)) :
    rdTWP [(6, fun fr σ => rdInv args σ0 fr σ ∧ rdVar args σ0 fr σ < v)] 20 37 fr σ := by
  unfold rdTWP
  jvc [rdTerm, rdInv, RdAt, rdVar, rdCallees, spacesSig, spacesSpecI]

end EquivLean.Modernize.Cbstm03a.Java.Term2
