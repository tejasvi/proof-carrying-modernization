import EquivLean.Modernize.Cbstm03a.Java.Mw.A

/-!
# CBSTM03A → Java: `memWrite`, a slot write from statement 26 to statement 30

`cur = slots[idx]`: a `null` slot gets `spaces(len)`, a string slot is used as it is; both reach statement 30.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space heap_grows keeps_trans keeps_of_grows GrowsK growsK_elim
  grows_split)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

/-- `SlotsAt` holds in a state where the heap only grew (cbA-mem's `slotsAt_grows`). -/
theorem slotsAt_grows' {σ σ' : State} {a : Addr} {m : Nat → JChar} (h : SlotsAt σ a m) (hg : Grows σ σ') :
    SlotsAt σ' a m := by
  obtain ⟨vs, ha, hl, hs⟩ := h
  refine ⟨vs, heap_grows hg ha, hl, fun i hi => ?_⟩
  rcases hs i hi with h1 | ⟨x, t, h1, h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr ⟨x, t, h1, heap_grows hg h2, h3, h4⟩

theorem memK_grows {σ0 σ σ' : State} {a : Addr} {off : I64} {t : JStr} {p : Nat} (hK : MemK σ0 σ a off t p)
    (hg : GrowsK σ σ') (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics) : MemK σ0 σ' a off t p := by
  unfold MemK at hK ⊢
  obtain ⟨hS, hk, hi0, hs0⟩ := hK
  exact ⟨fun m hm => slotsAt_grows' (hS m hm) (growsK_elim hg), keeps_trans hk (keeps_of_grows (growsK_elim hg)),
    hi.trans hi0, hs.trans hs0⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- A `null` slot: `cur#7 = spaces(len)`. -/
theorem mw_m26n_run (σ0 : State) (args : List Value) (Post : Outcome → Prop) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32) (idx len within take : I32) (vs : List Value)
    (i W K P : Nat)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h12 : fr.get 12 = some (.ref x))
    (h10 : fr.get 10 = some (.int pos)) (h5 : fr.get 5 = some (.int n))
    (h6 : fr.get 6 = some (.int idx)) (h7 : fr.get 7 = some (.int len)) (h8 : fr.get 8 = some (.int within))
    (h11 : fr.get 11 = some (.int take))
    (hidx : idx.toInt = i) (hl : len.toInt = slotLn i) (hw : within.toInt = W)
    (htk : take.toInt = K) (hL : slotLn i ≤ 334) (hi : i < 561)
    (ha : σ.heap a = some (.array (.cls "java.lang.String") vs)) (hvl : vs.length = 561)
    (hvn : vs[i]? = some .null) (hxs : σ.heap x = some (.str t)) (hinit : σ.initOf "Cbstm03a" = .done)
    (hK : MemK σ0 σ a off t P) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      ((30, A30 σ0 a off x t pos n vs i W K P (List.replicate (slotLn i) space)) :: memWriteInv.inst args σ0) Post
      100 26 fr σ := by
  jvc [memWriteInv, A30, mwCallees, spacesSpecI, grows_split]
  all_goals exact memK_grows hK ‹_› ‹_› ‹_›

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- A string slot: `cur#7 = cur`. -/
theorem mw_m26r_run (σ0 : State) (args : List Value) (Post : Outcome → Prop) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32) (idx len within take : I32) (vs : List Value)
    (i W K P : Nat) (y : Addr) (c : JStr)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h12 : fr.get 12 = some (.ref x))
    (h10 : fr.get 10 = some (.int pos)) (h5 : fr.get 5 = some (.int n))
    (h6 : fr.get 6 = some (.int idx)) (h7 : fr.get 7 = some (.int len)) (h8 : fr.get 8 = some (.int within))
    (h11 : fr.get 11 = some (.int take))
    (hidx : idx.toInt = i) (hl : len.toInt = slotLn i) (hw : within.toInt = W)
    (htk : take.toInt = K) (hL : slotLn i ≤ 334) (hi : i < 561)
    (ha : σ.heap a = some (.array (.cls "java.lang.String") vs)) (hvl : vs.length = 561)
    (hvr : vs[i]? = some (.ref y)) (hyc : σ.heap y = some (.str c)) (hxs : σ.heap x = some (.str t))
    (hinit : σ.initOf "Cbstm03a" = .done) (hK : MemK σ0 σ a off t P) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      ((30, A30 σ0 a off x t pos n vs i W K P c) :: memWriteInv.inst args σ0) Post 100 26 fr σ := by
  jvc [memWriteInv, A30, mwCallees]

end EquivLean.Modernize.Cbstm03a.Java.Mw

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_m26n_run
#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_m26r_run
