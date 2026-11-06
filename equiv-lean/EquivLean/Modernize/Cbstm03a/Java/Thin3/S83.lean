import EquivLean.Modernize.Cbstm03a.Java.Thin3.S93

/-!
# CBSTM03A → Java: `run`'s thin paths from cut point 80, statements 83 … 93

`Thin3.Seg83` (statement 83, after the three substrings of the record): the locals, the strings, `trnxTexts`,
`trnxSt`, `trct`, the slots array unchanged and every string of `σS` kept. From 83 (`Thin3.seg83`): the card
number test, `setTrct` when it changes, `cardOff`, then statement 93 (`Thin3.Seg93`, continued by `Thin3.seg93`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space heap_grows GrowsK
  growsK_elim grows_split fixStr_length)

attribute [-simp] List.reduceReplicate

attribute [local irreducible] EquivLean.Modernize.Cbstm03a.Java.SlotsAt

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

/-- Statement 83 of the paths from 80: the locals the rest reads, the strings, `trnxTexts` holding `txs`,
`trnxSt` = `{i1, 0}`, `trct` holding `tv`, the slots array unchanged and every string of `σS` kept. -/
def Seg83 (σS : State) (mem t1 st1 trct res : Addr) (txs : List Value) (i1 : I32) (tv : List Value) (fr : Frame)
    (σ : State) : Prop :=
  fr.get 16 = some (.ref mem) ∧ fr.get 11 = some (.ref t1) ∧ fr.get 1 = some (.ref st1) ∧
  fr.get 24 = some (.ref trct) ∧ fr.get 7 = some (.ref res) ∧
  (∃ c : I64, fr.get 18 = some (.long c)) ∧ (∃ c : I64, fr.get 17 = some (.long c)) ∧
  (∃ x s, fr.get 32 = some (.ref x) ∧ σ.heap x = some (.str s)) ∧
  (∃ x s, fr.get 36 = some (.ref x) ∧ σ.heap x = some (.str s)) ∧
  (∃ x s, fr.get 34 = some (.ref x) ∧ σ.heap x = some (.str s)) ∧
  (∃ x s, fr.get 33 = some (.ref x) ∧ σ.heap x = some (.str s)) ∧
  σ.heap t1 = some (.array (.cls "java.lang.String") txs) ∧
  σ.heap st1 = some (.array (.prim .int) [.int i1, .int 0]) ∧
  σ.heap trct = some (.array (.prim .long) tv) ∧
  σ.heap mem = σS.heap mem ∧ StrMono σS σ ∧ σ.initOf "Cbstm03a" = .done

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
/-- From statement 83: the card number test, `setTrct` when it changes, `cardOff`, statement 93. -/
theorem seg83 (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (σS : State) (mem t1 st1 trct res : Addr)
    (txs : List Value) (i1 : I32) (tv : List Value) (m : Nat → JChar) (hS : SlotsAt σS mem m)
    (hl : txs.length < 2147483648) (hi0 : 0 ≤ i1.toInt) (ht1m : t1 < mem) (hmt : mem < trct) (hts : trct < st1)
    (hv : vX80 + ((vN : Int) - i1.toInt).toNat ≤ v) (fr : Frame) (σ : State)
    (h : Seg83 σS mem t1 st1 trct res txs i1 tv fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA
      ((runInv g).map fun q => (q.1, fun fr' σ' => runVar q.1 args σ0 fr' σ' < v)) (fun _ => True) 280 83 fr σ := by
  obtain ⟨h16, h11, h1, h24, h7, ⟨cr, h18⟩, ⟨tr, h17⟩, ⟨x32, s32, h32, hx32⟩, ⟨xt, tt, h36, hxt⟩,
    ⟨xc, tc, h34, hxc⟩, ⟨xn, tn, h33, hxn⟩, ht1, hst1, htr, hmem, hsm, hci⟩ := h
  have hS' : SlotsAt σ mem m := slotsAt_mono hS hmem hsm
  clear hS hmem hsm
  have hdead : ∀ σ' : State, σ'.initOf "Cbstm03a" = InitSt.none → (∀ c, σ'.initOf c = σ.initOf c) → False :=
    fun σ' e1 e2 => by rw [e2, hci] at e1; cases e1
  have htm : trct ≠ mem := Nat.ne_of_gt hmt
  have ht1t : t1 ≠ trct := Nat.ne_of_lt (Nat.lt_trans ht1m hmt)
  have hst1t : st1 ≠ trct := Nat.ne_of_gt hts
  have hxtt : xt ≠ trct := ne_of_heap hxt htr (by simp)
  have hxct : xc ≠ trct := ne_of_heap hxc htr (by simp)
  have hxnt : xn ≠ trct := ne_of_heap hxn htr (by simp)
  refine bodyWP_cut_insert (callWPThin_mono _ _ 1) _ _ _ 93 (by rfl) (Seg93 σ mem t1 st1 trct res txs i1) 200
    (by
      intro fr' σ' h
      exact seg93 g args σ0 v σ mem t1 st1 trct res txs i1 m hS' tv htr hl hi0 ht1m hmt hts hv fr' σ' h)
    80 83 fr σ ?_
  clear hv hS'
  jvc [runCallees, runInv, Seg93, keeps_split]

end EquivLean.Modernize.Cbstm03a.Java.Thin3
