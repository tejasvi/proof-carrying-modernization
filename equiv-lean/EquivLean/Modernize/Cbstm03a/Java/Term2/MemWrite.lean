import EquivLean.Modernize.Cbstm03a.Java.Term2.Cut

/-!
# CBSTM03A → Java, termination: `memWrite` (definitions and the paths without slot access)

One loop, head statement 5 (`if pos >= n`). Locals: `slots` 0, `off` 1, `o` 2, `n` 5, `idx` 6, `len` 7,
`within` 8, `pos` 10, `take` 11, `s` 12, `cur#7` 15. Variant `2^31 - pos`: a negative offset sets `pos = -off`
(above `pos`, as `off + pos < 0` and `off > -2^31`), a slot step adds `take ≥ 1` (`within < len` by the slot
geometry, `pos < n`). Calls by contract (`memCallees`, the contracts of `CbAMem.Iface2`/`CbANum.Iface1`):
`slotIndex`, `slotLen`, `slotStart`, `spaces` (`n ≤ 2^30`: a slot length).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

/-- The callees of `memWrite` and `memRead`. -/
def memCallees : Contracts :=
  [(slotIndexSig, slotIndexSpec), (slotLenSig, slotLenSpec), (slotStartSig, slotStartSpec),
   (spacesSig, spacesSpecI)]

/-- `memWrite`'s loop head. -/
def WrAt (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr) (t : JStr) (vs : List Value)
    (n pos : I32) : Prop :=
  fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 5 = some (.int n) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref x) ∧
  σ.heap x = some (.str t) ∧ σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ SlotOk σ vs ∧
  -2147483648 < off.toInt ∧ 0 ≤ pos.toInt ∧ (pos.toInt = 0 ∨ off.toInt < 171156) ∧
  σ.initOf "Cbstm03a" = .done

def wrInv (args : List Value) (_ : State) (fr : Frame) (σ : State) : Prop :=
  ∃ a off x t vs n pos, args = [.ref a, .long off, .ref x] ∧ WrAt fr σ a off x t vs n pos

def wrVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 10 with
  | some (.int p) => (2147483648 - p.toInt).toNat
  | _ => 0

def wrTerm : TermCuts := [(5, wrInv, wrVar)]

/-- The termination paths of `memWrite` from statement `pc`, cut assertions `I`, `fuel` statements. -/
@[irreducible] def wrTWP (I : Cuts) (fuel pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPT Gen.prog (memCallees.env.below (fun _ => 0) 1) 0)
    Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)» I (fun _ => True) fuel pc fr σ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem wr_tentry (args : List Value) (σ0 : State) (a : Addr) (off : I64) (x : Addr) (t : JStr)
    (vs : List Value) (ha : args = [.ref a, .long off, .ref x]) (hx : σ0.heap x = some (.str t))
    (hav : σ0.heap a = some (.array (.cls "java.lang.String") vs)) (hok : SlotOk σ0 vs)
    (hoff : -2147483648 < off.toInt) (hinit : σ0.initOf "Cbstm03a" = .done) :
    wrTWP (wrTerm.inv args σ0) 60 0 (Frame.init true args) σ0 := by
  subst ha
  unfold wrTWP
  jvc [wrTerm, wrInv, WrAt, wrVar, memCallees]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem wr_texit (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (h : WrAt fr σ a off x t vs n pos) (hx : n.toInt ≤ pos.toInt) :
    wrTWP (wrTerm.dec args σ0 (wrVar args σ0 fr σ)) 60 5 fr σ := by
  unfold wrTWP
  jvc [wrTerm, wrInv, WrAt, wrVar, memCallees]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem wr_tneg (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (ha : args = [.ref a, .long off, .ref x])
    (h : WrAt fr σ a off x t vs n pos) (hx : pos.toInt < n.toInt)
    (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt) (hneg : off.toInt + pos.toInt < 0)
    (hp : (JLong.toInt (-off)).toInt = -off.toInt) :
    wrTWP (wrTerm.dec args σ0 (wrVar args σ0 fr σ)) 60 5 fr σ := by
  unfold wrTWP
  jvc [wrTerm, wrInv, WrAt, wrVar, memCallees]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem wr_tpast (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (h : WrAt fr σ a off x t vs n pos) (hx : pos.toInt < n.toInt)
    (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt) (hpast : 171156 ≤ off.toInt + pos.toInt)
    (hz : ¬(off + JInt.toLong pos = 0#64)) :
    wrTWP (wrTerm.dec args σ0 (wrVar args σ0 fr σ)) 60 5 fr σ := by
  unfold wrTWP
  jvc [wrTerm, wrInv, WrAt, wrVar, memCallees]

end EquivLean.Modernize.Cbstm03a.Java.Term2

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term2.wr_tentry
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term2.wr_texit
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term2.wr_tneg
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term2.wr_tpast
