import EquivLean.Modernize.Cbstm03a.Java.Mw.Defs

/-!
# CBSTM03A → Java: `memWrite`, the skip below 0

`off + pos < 0`: `pos = (int) -off`, back to the loop head (the characters below position 0 are dropped).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

/-- `MemK` after the skip: nothing below 0 is written. -/
theorem memK_skip {σ0 σ : State} {a : Addr} {off : I64} {t : JStr} {p : Nat} (hK : MemK σ0 σ a off t p)
    (h : off.toInt + p ≤ 0) : MemK σ0 σ a off t (-off.toInt).toNat := by
  unfold MemK at hK ⊢
  obtain ⟨hS, hk, hi, hs⟩ := hK
  refine ⟨fun m hm => ?_, hk, hi, hs⟩
  have e1 := memWr_neg m off.toInt t p h
  have e2 := memWr_neg m off.toInt t (-off.toInt).toNat (by omega)
  rw [e2]
  have := hS m hm
  rw [e1] at this
  exact this

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- `off + pos < 0`: `pos = (int) -off`, the loop head. -/
theorem mw_skip_run (σ0 : State) (Post : Outcome → Prop) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h12 : fr.get 12 = some (.ref x))
    (h10 : fr.get 10 = some (.int pos)) (h5 : fr.get 5 = some (.int n))
    (hxs : σ.heap x = some (.str t)) (hx0 : σ0.heap x = some (.str t)) (hn : n.toInt = t.length)
    (htl : t.length < 2147483648) (hoff : -2147483648 < off.toInt) (hinit : σ.initOf "Cbstm03a" = .done)
    (hx : pos.toInt < n.toInt) (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt)
    (hneg : off.toInt + pos.toInt < 0) (hoff0 : off.toInt < 0) (hlt : off.toInt < 171156)
    (hpn : (JLong.toInt (-off)).toInt = -off.toInt) (hK : MemK σ0 σ a off t (-off.toInt).toNat) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      (memWriteInv.inst [.ref a, .long off, .ref x] σ0) Post
      120 5 fr σ := by
  jvc [memWriteInv, mwInv5, MwAt, mwCallees]

theorem mw_skip (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32)
    (ha : args = [.ref a, .long off, .ref x]) (h : MwAt σ0 fr σ a off x t pos n)
    (hx : pos.toInt < n.toInt) (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt)
    (hneg : off.toInt + pos.toInt < 0) : mwWPc args σ0 [] 120 5 fr σ := by
  obtain ⟨h0, h1, h12, h10, h5, hxs, hx0, hn, htl, hoff, hp0, hpo, hinit, hK⟩ := h
  subst ha
  unfold mwWPc
  have hoff0 : off.toInt < 0 := by omega
  exact mw_skip_run σ0 _ fr σ a off x t pos n h0 h1 h12 h10 h5 hxs hx0 hn htl hoff hinit hx ho hneg hoff0
    (by omega) (neg_l2i_toInt off hoff hoff0) (memK_skip hK (by omega))

end EquivLean.Modernize.Cbstm03a.Java.Mw

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_skip
