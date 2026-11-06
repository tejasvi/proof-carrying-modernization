import EquivLean.Modernize.Cbstm03a.Java.Mw.Defs

/-!
# CBSTM03A → Java: `memWrite`, the exits from the loop head

`pos ≥ n` and `off + pos ≥ MEM_SZ` return. The paths are run against an arbitrary postcondition `Post` that holds
of the outcome (the symbolic executor never sees `memWriteSpec`'s `SlotsAt`); `post_of_memK` gives it.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

/-- At an exit with all of `t` written, `memWrite`'s postcondition. -/
theorem post_of_memK {σ0 σ : State} {a : Addr} {off : I64} {x : Addr} {t : JStr} {p : Nat}
    (hK : MemK σ0 σ a off t p) (hp : ∀ m, memWr m off.toInt (t.take p) = memWr m off.toInt t)
    (hx0 : σ0.heap x = some (.str t)) :
    memWriteSpec.post [.ref a, .long off, .ref x] σ0 (.normal none σ) := by
  unfold MemK at hK
  obtain ⟨hS, hk, hi, hs⟩ := hK
  simp only [memWriteSpec, Spec.of]
  intro a' off' x' m t' he hm ht
  simp only [List.cons.injEq, Value.ref.injEq, Value.long.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rw [hx0] at ht
  cases ht
  refine ⟨?_, by rw [← hp m]; exact hS m hm, hk, hi, hs⟩
  first | trivial | rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- `pos ≥ n`: the loop ends. -/
theorem mw_exit_run (args : List Value) (σ0 : State) (Post : Outcome → Prop) (fr : Frame) (σ : State) (pos n : I32)
    (h10 : fr.get 10 = some (.int pos)) (h5 : fr.get 5 = some (.int n)) (hx : n.toInt ≤ pos.toInt)
    (hP : Post (.normal none σ)) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      (memWriteInv.inst args σ0) Post 120 5 fr σ := by
  jvc [memWriteInv, mwCallees]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- `off + pos ≥ MEM_SZ`: the rest falls past the memory, the loop ends. -/
theorem mw_past_run (args : List Value) (σ0 : State) (Post : Outcome → Prop) (fr : Frame) (σ : State) (off : I64)
    (pos n : I32) (h1 : fr.get 1 = some (.long off)) (h10 : fr.get 10 = some (.int pos))
    (h5 : fr.get 5 = some (.int n)) (hx : pos.toInt < n.toInt)
    (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt) (hpast : 171156 ≤ off.toInt + pos.toInt)
    (hne : ¬ off + JInt.toLong pos = 0#64) (hP : Post (.normal none σ)) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      (memWriteInv.inst args σ0) Post 120 5 fr σ := by
  jvc [memWriteInv, mwCallees]

theorem mw_exit (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32)
    (ha : args = [.ref a, .long off, .ref x]) (h : MwAt σ0 fr σ a off x t pos n)
    (hx : n.toInt ≤ pos.toInt) : mwWPc args σ0 [] 120 5 fr σ := by
  obtain ⟨h0, h1, h12, h10, h5, hxs, hx0, hn, htl, hoff, hp0, hpo, hinit, hK⟩ := h
  subst ha
  unfold mwWPc
  exact mw_exit_run _ σ0 _ fr σ pos n h10 h5 hx
    (post_of_memK hK (fun m => memWr_take_full m _ t _ (by omega)) hx0)

theorem mw_past (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32)
    (ha : args = [.ref a, .long off, .ref x]) (h : MwAt σ0 fr σ a off x t pos n)
    (hx : pos.toInt < n.toInt) (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt)
    (hpast : 171156 ≤ off.toInt + pos.toInt) : mwWPc args σ0 [] 120 5 fr σ := by
  obtain ⟨h0, h1, h12, h10, h5, hxs, hx0, hn, htl, hoff, hp0, hpo, hinit, hK⟩ := h
  subst ha
  unfold mwWPc
  have hne : ¬ off + JInt.toLong pos = 0#64 := fun e => by
    rw [e] at ho
    have : (0#64 : BitVec 64).toInt = 0 := rfl
    omega
  exact mw_past_run _ σ0 _ fr σ off pos n h1 h10 h5 hx ho hpast hne
    (post_of_memK hK (fun m => memWr_past m _ t _ (by omega)) hx0)

end EquivLean.Modernize.Cbstm03a.Java.Mw

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_exit
#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_past
