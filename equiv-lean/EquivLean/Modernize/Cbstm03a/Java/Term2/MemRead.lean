import EquivLean.Modernize.Cbstm03a.Java.Term2.SlotLem

/-!
# CBSTM03A → Java, termination: `memRead` (definitions and the paths without slot access)

One loop, head statement 6 (`if pos >= n`). Locals: `slots` 0, `off` 1, `o` 2, `n` 5, `within` 6, `len` 7,
`skip` 9, `pos` 10, `take#8` 11, `sb` 12, `cur` 13. Variant `2^31 - pos`: a negative offset adds
`skip = min(-o, n - pos) ≥ 1`, a slot step adds `take ≥ 1`. Calls by contract (`memCallees`): `slotIndex`,
`slotLen`, `slotStart`, `spaces` (`n ≤ 2^30`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

/-- The callees of `memRead` (those of `memWrite`). -/
def rdCallees : Contracts :=
  [(slotIndexSig, slotIndexSpec), (slotLenSig, slotLenSpec), (slotStartSig, slotStartSpec),
   (spacesSig, spacesSpecI)]

/-- `memRead`'s loop head. -/
def RdAt (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr) (b : JStr) (vs : List Value)
    (n pos : I32) : Prop :=
  fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 5 = some (.int n) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref sb) ∧
  σ.heap sb = some (.builder "java.lang.StringBuilder" b) ∧
  σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ SlotOk σ vs ∧
  -2147483648 < off.toInt ∧ 0 ≤ pos.toInt ∧ (pos.toInt = 0 ∨ off.toInt < 171156) ∧ n.toInt ≤ 1073741824 ∧
  σ.initOf "Cbstm03a" = .done

def rdInv (args : List Value) (_ : State) (fr : Frame) (σ : State) : Prop :=
  ∃ a off sb b vs n pos, args = [.ref a, .long off, .int n] ∧ RdAt fr σ a off sb b vs n pos

def rdVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 10 with
  | some (.int p) => (2147483648 - p.toInt).toNat
  | _ => 0

def rdTerm : TermCuts := [(6, rdInv, rdVar)]

/-- The termination paths of `memRead` from statement `pc`, cut assertions `I`, `fuel` statements. -/
@[irreducible] def rdTWP (I : Cuts) (fuel pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPT Gen.prog (rdCallees.env.below (fun _ => 0) 1) 0)
    Gen.Cbstm03a.«memRead(java.lang.String[],long,int)» I (fun _ => True) fuel pc fr σ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem rd_tentry (args : List Value) (σ0 : State) (a : Addr) (off : I64) (n : I32)
    (vs : List Value) (ha : args = [.ref a, .long off, .int n])
    (hav : σ0.heap a = some (.array (.cls "java.lang.String") vs)) (hok : SlotOk σ0 vs)
    (hoff : -2147483648 < off.toInt) (hn : n.toInt ≤ 1073741824) (hinit : σ0.initOf "Cbstm03a" = .done) :
    rdTWP (rdTerm.inv args σ0) 60 0 (Frame.init true args) σ0 := by
  subst ha
  unfold rdTWP
  jvc [rdTerm, rdInv, RdAt, rdVar, rdCallees]
  all_goals
    refine slotOk_keep hok ?_
    repeat (first | exact strKeep_refl _ | refine strKeep_alloc ?_ _ |
      refine strKeep_setObj ?_ (fun s e => by rw [State.heap_next] at e; cases e) _)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem rd_texit (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr)
    (b : JStr) (vs : List Value) (n pos : I32) (h : RdAt fr σ a off sb b vs n pos) (hx : n.toInt ≤ pos.toInt) :
    rdTWP (rdTerm.dec args σ0 (rdVar args σ0 fr σ)) 60 6 fr σ := by
  unfold rdTWP
  jvc [rdTerm, rdInv, RdAt, rdVar, rdCallees]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem rd_tneg (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr)
    (b : JStr) (vs : List Value) (n pos : I32) (ha : args = [.ref a, .long off, .int n])
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h5 : fr.get 5 = some (.int n))
    (h10 : fr.get 10 = some (.int pos)) (h12 : fr.get 12 = some (.ref sb))
    (hsb : σ.heap sb = some (.builder "java.lang.StringBuilder" b))
    (hav : σ.heap a = some (.array (.cls "java.lang.String") vs)) (hok : SlotOk σ vs)
    (hoff : -2147483648 < off.toInt) (hp0 : 0 ≤ pos.toInt) (hn : n.toInt ≤ 1073741824)
    (hinit : σ.initOf "Cbstm03a" = .done) (hx : pos.toInt < n.toInt)
    (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt) (hneg : off.toInt + pos.toInt < 0)
    (hsk : (JLong.toInt (-(off + JInt.toLong pos))).toInt = -(off.toInt + pos.toInt))
    (hsk2 : (JLong.toInt (-JInt.toLong pos + -off)).toInt = -(off.toInt + pos.toInt)) :
    rdTWP (rdTerm.dec args σ0 (rdVar args σ0 fr σ)) 60 6 fr σ := by
  subst ha
  unfold rdTWP
  jvc [rdTerm, rdInv, RdAt, rdVar, rdCallees, spacesSig, spacesSpecI]
  all_goals
    refine slotOk_keep hok ?_
    repeat (first | exact strKeep_refl _ | refine strKeep_alloc ?_ _ |
      refine strKeep_setObj ?_ (fun s e => by rw [hsb] at e; cases e) _ | exact strKeep_of_frame ‹_›)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem rd_tpast (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr)
    (b : JStr) (vs : List Value) (n pos : I32) (h : RdAt fr σ a off sb b vs n pos) (hx : pos.toInt < n.toInt)
    (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt) (hpast : 171156 ≤ off.toInt + pos.toInt)
    (hz : ¬(off + JInt.toLong pos = 0#64)) :
    rdTWP (rdTerm.dec args σ0 (rdVar args σ0 fr σ)) 60 6 fr σ := by
  unfold rdTWP
  jvc [rdTerm, rdInv, RdAt, rdVar, rdCallees, spacesSig, spacesSpecI]

end EquivLean.Modernize.Cbstm03a.Java.Term2
