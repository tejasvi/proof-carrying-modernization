import EquivLean.Modernize.Cbstm03a.Java.Mw.M26

/-!
# CBSTM03A → Java: `memWrite`, a slot write from statement 30 to statement 36

`cur#7` holds the slot's text `c`: the new slot text `c[0, within) + s[pos, pos + take) + c[within + take, …)`
(three `substring`s and a concatenation, four new strings), cut at statement 36 (`slots[idx] = cur`: `A36`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space heap_grows keeps_trans keeps_of_grows GrowsK growsK_elim
  grows_split)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

/-- Statement 36: `cur` holds the new slot text. -/
def A36 (σ0 : State) (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32) (vs : List Value) (i W K P : Nat)
    (c : JStr) (fr : Frame) (σ : State) : Prop :=
  fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 5 = some (.int n) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref x) ∧
  (∃ idx take : I32, fr.get 6 = some (.int idx) ∧ fr.get 11 = some (.int take) ∧ idx.toInt = i ∧ take.toInt = K) ∧
  (∃ q, fr.get 13 = some (.ref q) ∧
    σ.heap q = some (.str (c.take W ++ ((t.take (P + K)).drop P ++ c.drop (W + K))))) ∧
  σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ σ.heap x = some (.str t) ∧
  σ.initOf "Cbstm03a" = .done ∧ MemK σ0 σ a off t P

theorem memK_alloc {σ0 σ : State} {a : Addr} {off : I64} {t : JStr} {p : Nat} (hK : MemK σ0 σ a off t p) (o : Obj) :
    MemK σ0 (σ.alloc o).2 a off t p := by
  have hg : Grows σ (σ.alloc o).2 :=
    ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun y hy => State.heap_alloc_of_lt hy o⟩
  unfold MemK at hK ⊢
  obtain ⟨hS, hk, hi, hs⟩ := hK
  exact ⟨fun m hm => slotsAt_grows' (hS m hm) hg, keeps_trans hk (keeps_of_grows hg), hi, hs⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.modelContracts true in
theorem mw_m30_run (σ0 : State) (args : List Value) (Post : Outcome → Prop) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32) (idx within take : I32) (vs : List Value)
    (i W K P : Nat) (y : Addr) (c : JStr)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.long off)) (h12 : fr.get 12 = some (.ref x))
    (h10 : fr.get 10 = some (.int pos)) (h5 : fr.get 5 = some (.int n))
    (h6 : fr.get 6 = some (.int idx)) (h8 : fr.get 8 = some (.int within)) (h11 : fr.get 11 = some (.int take))
    (h15 : fr.get 15 = some (.ref y))
    (hidx : idx.toInt = i) (hw : within.toInt = W) (htk : take.toInt = K) (hp : pos.toInt = P)
    (hWK : W + K ≤ slotLn i) (hL : slotLn i ≤ 334) (hcl : c.length = slotLn i) (hPK : P + K ≤ t.length)
    (htl : t.length < 2147483648)
    (hpt : (pos + take).toInt = ((P + K : Nat) : Int)) (hwt : (within + take).toInt = ((W + K : Nat) : Int))
    (ha : σ.heap a = some (.array (.cls "java.lang.String") vs)) (hyc : σ.heap y = some (.str c))
    (hxs : σ.heap x = some (.str t)) (hinit : σ.initOf "Cbstm03a" = .done) (hK : MemK σ0 σ a off t P) :
    bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      ((36, A36 σ0 a off x t pos n vs i W K P c) :: memWriteInv.inst args σ0) Post 100 30 fr σ := by
  jvc [memWriteInv, A36]
  all_goals
    repeat (with_reducible refine memK_alloc ?_ _)
    exact hK

end EquivLean.Modernize.Cbstm03a.Java.Mw

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_m30_run
