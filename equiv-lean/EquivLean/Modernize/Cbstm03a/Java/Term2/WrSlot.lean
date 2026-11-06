import EquivLean.Modernize.Cbstm03a.Java.Term2.MemWrite

/-!
# CBSTM03A → Java, termination: `memWrite`'s slot step, in three segments

Extra cut points (`bodyWP_cutT`) at statement 17 (`slotIndex(o)`: the offset `o` as a variable) and 26
(`cur = slots[idx]`: the step `take` as a variable with `1 ≤ take ≤ n - pos`). The call results of the slot
helpers are variables with their values' facts (`i`, `l`, `s`, `w`: index, length, start, offset in the slot).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

/-- At statement 17: the offset `o = off + pos` in `[0, MEM_SZ)`. -/
def WrO (a : Addr) (off : I64) (x : Addr) (t : JStr) (vs : List Value) (n pos : I32) (fr : Frame) (σ : State) :
    Prop :=
  ∃ o : I64, fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 2 = some (.long o) ∧
    fr.get 5 = some (.int n) ∧ fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref x) ∧
    σ.heap x = some (.str t) ∧ σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ SlotOk σ vs ∧
    -2147483648 < off.toInt ∧ off.toInt < 171156 ∧ 0 ≤ pos.toInt ∧ pos.toInt < n.toInt ∧
    0 ≤ o.toInt ∧ o.toInt < 171156 ∧ σ.initOf "Cbstm03a" = .done

/-- At statement 26: the step `take`, `1 ≤ take ≤ n - pos`; the slot length at most `2^30`. -/
def WrTk (a : Addr) (off : I64) (x : Addr) (t : JStr) (vs : List Value) (n pos : I32) (fr : Frame) (σ : State) :
    Prop :=
  ∃ idx len within take : I32, fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧
    fr.get 5 = some (.int n) ∧ fr.get 6 = some (.int idx) ∧ fr.get 7 = some (.int len) ∧
    fr.get 8 = some (.int within) ∧ fr.get 10 = some (.int pos) ∧ fr.get 11 = some (.int take) ∧
    fr.get 12 = some (.ref x) ∧
    σ.heap x = some (.str t) ∧ σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ SlotOk σ vs ∧
    -2147483648 < off.toInt ∧ off.toInt < 171156 ∧ 0 ≤ pos.toInt ∧ 1 ≤ take.toInt ∧
    take.toInt ≤ n.toInt - pos.toInt ∧ len.toInt ≤ 1073741824 ∧ σ.initOf "Cbstm03a" = .done

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
/-- Statements 5 … 17 of a slot step. -/
theorem wr_tslot5 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (v : Nat)
    (h : WrAt fr σ a off x t vs n pos) (hx : pos.toInt < n.toInt)
    (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt) (h0 : 0 ≤ off.toInt + pos.toInt)
    (h1 : off.toInt + pos.toInt < 171156) :
    wrTWP ((17, WrO a off x t vs n pos) ::
      [(5, fun fr σ => wrInv args σ0 fr σ ∧ wrVar args σ0 fr σ < v)]) 20 5 fr σ := by
  unfold wrTWP
  jvc [wrTerm, wrInv, WrAt, wrVar, memCallees, WrO]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
/-- Statements 17 … 26: the slot helpers. -/
theorem wr_tslot17 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (v : Nat) (o : I64) (k : Nat) (i l w : I32) (s : I64)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h2 : fr.get 2 = some (.long o))
    (h5 : fr.get 5 = some (.int n)) (h10 : fr.get 10 = some (.int pos)) (h12 : fr.get 12 = some (.ref x))
    (hx : σ.heap x = some (.str t)) (hav : σ.heap a = some (.array (.cls "java.lang.String") vs))
    (hok : SlotOk σ vs) (hoff0 : -2147483648 < off.toInt) (hoff1 : off.toInt < 171156) (hp0 : 0 ≤ pos.toInt)
    (hpn : pos.toInt < n.toInt) (ho0 : 0 ≤ o.toInt) (ho1 : o.toInt < 171156)
    (hinit : σ.initOf "Cbstm03a" = .done)
    (hk : slotIdx o.toNat = k) (hi : BitVec.ofNat 32 k = i) (hl : BitVec.ofNat 32 (slotLn i.toNat) = l)
    (hs : BitVec.ofNat 64 (slotSt i.toNat) = s) (hw : JLong.toInt (o - s) = w)
    (hit : i.toInt = k) (hk1 : k < 561) (hl1 : 16 ≤ l.toInt) (hl2 : l.toInt ≤ 334) (hw0 : 0 ≤ w.toInt)
    (hwl : w.toInt < l.toInt) :
    wrTWP ((26, WrTk a off x t vs n pos) ::
      [(5, fun fr σ => wrInv args σ0 fr σ ∧ wrVar args σ0 fr σ < v)]) 20 17 fr σ := by
  unfold wrTWP
  jvc [wrTerm, wrInv, WrAt, wrVar, memCallees, WrTk, slotIndexSig, slotIndexSpec, slotLenSig, slotLenSpec,
    slotStartSig, slotStartSpec]

end EquivLean.Modernize.Cbstm03a.Java.Term2
