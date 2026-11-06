import EquivLean.Modernize.Cbstm03a.Java.Mw.A

/-!
# CBSTM03A → Java: `memWrite`, a slot write from the loop head to statement 14

`0 ≤ o = off + pos < MEM_SZ`: `o cmp 0` is `0` or `1` (two paths), both reach `label2` (statement 14).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem mw_m5_run (args : List Value) (σ0 : State) (Post : Outcome → Prop) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (pos n : I32) (J : Nat)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h12 : fr.get 12 = some (.ref x))
    (h10 : fr.get 10 = some (.int pos)) (h5 : fr.get 5 = some (.int n))
    (hx : pos.toInt < n.toInt) (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt)
    (hJ : off.toInt + pos.toInt = J) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      ((14, A14 σ a off x pos n J) :: memWriteInv.inst args σ0) Post 100 5 fr σ := by
  jvc [memWriteInv, A14]

end EquivLean.Modernize.Cbstm03a.Java.Mw

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_m5_run
