import EquivLean.Modernize.Cbstm03a.Java.Mw.A

/-!
# CBSTM03A → Java: `memWrite`, a slot write from statement 14 to statement 22

`o = J < MEM_SZ`: `slotIndex(o)` is slot `i`, `slotLen`, `slotStart`, `within = (int) (o - slotStart(i))`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem mw_m14_run (args : List Value) (σ0 : State) (Post : Outcome → Prop) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (pos n : I32) (o : I64) (J i : Nat)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h12 : fr.get 12 = some (.ref x))
    (h10 : fr.get 10 = some (.int pos)) (h5 : fr.get 5 = some (.int n)) (h2 : fr.get 2 = some (.long o))
    (hinit : σ.initOf "Cbstm03a" = .done)
    (ho : o.toInt = J) (hon : o.toNat = J) (hJm : J < 171156) (hiJ : slotIdx J = i) (hi : i < 561)
    (hL : slotLn i ≤ 334) (hw0 : slotSt i ≤ J) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      ((22, A22 σ a off x pos n i (J - slotSt i)) :: memWriteInv.inst args σ0) Post 100 14 fr σ := by
  jvc [memWriteInv, A22, mwCallees, slotIndexSpec, slotLenSpec, slotStartSpec]
  all_goals
    apply valI_intro
    rw [within_toInt _ _ _ ‹_› ‹_› ‹_›]
    omega

end EquivLean.Modernize.Cbstm03a.Java.Mw

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_m14_run
