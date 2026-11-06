import EquivLean.Modernize.Cbstm03a.Java.Mw.A

/-!
# CBSTM03A → Java: `memWrite`, a slot write from statement 22 to statement 26

`take = len - within`, cut to `n - pos` when that is smaller (two paths, both reach statement 26).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

theorem sub_toInt32 (a b : I32) (h1 : -2147483648 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt < 2147483648) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [BitVec.toInt_sub]
  exact bmod32_self h1 h2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem mw_m22_run (args : List Value) (σ0 : State) (Post : Outcome → Prop) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (pos n : I32) (idx len within : I32) (i W K : Nat)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h12 : fr.get 12 = some (.ref x))
    (h10 : fr.get 10 = some (.int pos)) (h5 : fr.get 5 = some (.int n))
    (h6 : fr.get 6 = some (.int idx)) (h7 : fr.get 7 = some (.int len)) (h8 : fr.get 8 = some (.int within))
    (hidx : idx.toInt = i) (hl : len.toInt = slotLn i) (hw : within.toInt = W) (hL : slotLn i ≤ 334)
    (hWL : W < slotLn i) (hx : pos.toInt < n.toInt) (hp0 : 0 ≤ pos.toInt) (hn31 : n.toInt < 2147483648)
    (hK1 : (K : Int) ≤ slotLn i - W) (hK2 : (K : Int) ≤ n.toInt - pos.toInt)
    (hK3 : (K : Int) = slotLn i - W ∨ (K : Int) = n.toInt - pos.toInt) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      ((26, A26 σ a off x pos n i W K) :: memWriteInv.inst args σ0) Post 100 22 fr σ := by
  have e1 : (len - within).toInt = len.toInt - within.toInt := sub_toInt32 len within (by omega) (by omega)
  have e2 : (n - pos).toInt = n.toInt - pos.toInt := sub_toInt32 n pos (by omega) (by omega)
  jvc [memWriteInv, A26]
  all_goals
    apply valI_intro
    omega

end EquivLean.Modernize.Cbstm03a.Java.Mw

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_m22_run
