import EquivLean.Modernize.Cbstm03a.Java.Mw.A

/-!
# CBSTM03A → Java: `memWrite`, a slot write from statement 36 back to the loop head

`slots[idx] = cur`, `pos = pos + take`: the loop head, with the slots array updated (`MemK` of the new state given).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem mw_m36_run (σ0 : State) (Post : Outcome → Prop) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (t c' : JStr) (pos n idx take : I32) (vs : List Value) (i K P : Nat) (q : Addr)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h12 : fr.get 12 = some (.ref x))
    (h10 : fr.get 10 = some (.int pos)) (h5 : fr.get 5 = some (.int n))
    (h6 : fr.get 6 = some (.int idx)) (h11 : fr.get 11 = some (.int take)) (h13 : fr.get 13 = some (.ref q))
    (hidx : idx.toInt = i) (hi : i < 561) (hvl : vs.length = 561) (htk : take.toInt = K) (hp : pos.toInt = P)
    (hpt : (pos + take).toInt = ((P + K : Nat) : Int))
    (ha : σ.heap a = some (.array (.cls "java.lang.String") vs)) (hq : σ.heap q = some (.str c'))
    (hxs : σ.heap x = some (.str t)) (hx0 : σ0.heap x = some (.str t)) (hn : n.toInt = t.length)
    (htl : t.length < 2147483648) (hoff : -2147483648 < off.toInt) (hlt : off.toInt < 171156)
    (hinit : σ.initOf "Cbstm03a" = .done)
    (hK' : MemK σ0 (σ.setObj a (.array (.cls "java.lang.String") (vs.set i (.ref q)))) a off t (P + K)) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      (memWriteInv.inst [.ref a, .long off, .ref x] σ0) Post 100 36 fr σ := by
  jvc [memWriteInv, mwInv5, MwAt]

end EquivLean.Modernize.Cbstm03a.Java.Mw

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_m36_run
