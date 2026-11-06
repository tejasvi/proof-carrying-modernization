import EquivLean.Modernize.Cbstm03a.Java.Thin3.Lem

/-!
# CBSTM03A → Java: `run`'s thin paths from cut point 52, the exit path from statement 61 on

`Thin3.Seg61` (statement 61, after the three new arrays): `trnxTexts`, `trnxSt` = `{0, 0}`. `seqRead` answers
`"00"` (records left: `trnxSt` = `{1, 0}`) or `"10"` (none: the run abends). With records left the path is split
again at statement 69 (`Thin3.Seg69`, after `fix`): the record text is generalized to a string of 1000 characters,
so that the string models (`substring`'s bounds) never meet `fixStr … 1000` itself; from 69 the path reaches cut
point 80 with the variant `vX80 + (2^31 − 1)`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space heap_grows GrowsK
  growsK_elim grows_split fixStr_length)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

/-- Statement 61 of the exit path from 52: `trnxTexts` holds `txs`, `trnxSt` a new `{0, 0}`. -/
def Seg61 (t1 res : Addr) (txs : List Value) (fr : Frame) (σ : State) : Prop :=
  ∃ st1 : Addr, fr.get 11 = some (.ref t1) ∧ fr.get 1 = some (.ref st1) ∧ fr.get 7 = some (.ref res) ∧
    σ.heap t1 = some (.array (.cls "java.lang.String") txs) ∧
    σ.heap st1 = some (.array (.prim .int) [.int 0, .int 0]) ∧ t1 < st1 ∧ σ.initOf "Cbstm03a" = .done

/-- Statement 69 with records left: `tRest` = `"00"`, `cn` a string of 1000 characters, `trnxSt` = `{1, 0}`. -/
def Seg69 (st1 : Addr) (fr : Frame) (σ : State) : Prop :=
  (∃ w, fr.get 32 = some (.ref w) ∧ σ.heap w = some (.str (JStr.ofString "00"))) ∧
  (∃ x s, fr.get 33 = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length = 1000) ∧
  fr.get 1 = some (.ref st1) ∧ σ.heap st1 = some (.array (.prim .int) [.int 1, .int 0]) ∧
  σ.initOf "Cbstm03a" = .done

theorem str00_ne_10 : ¬ JStr.ofString "00" = JStr.ofString "10" := by decide +kernel
theorem str04_ne_10 : ¬ JStr.ofString "04" = JStr.ofString "10" := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 3000000 in
/-- From statement 69: `"00".equals("00")`, the record's first 350 and 16 characters, cut point 80. -/
theorem seg69 (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (st1 : Addr) (hv : vX80 + vN < v)
    (fr : Frame) (σ : State) (h : Seg69 st1 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA
      ((runInv g).map fun q => (q.1, fun fr' σ' => runVar q.1 args σ0 fr' σ' < v)) (fun _ => True) 100 69 fr σ := by
  obtain ⟨⟨w, h32, hw⟩, ⟨x, s, h33, hx, hs⟩, h1, hst1, hci⟩ := h
  simp only [vX80, vM, vC3, vC4, vK, vN] at hv
  jvc [runCallees, runInv, runVar, arr0, vN, vM, vC3, vC4, vK, vX80]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 3000000 in
/-- From statement 61: `spaces`, `seqRead`; records left: `fix` of record 0, then statement 69; none: an abend. -/
theorem seg61 (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (t1 res : Addr) (txs : List Value)
    (hl : txs.length < 2147483648) (hv : vX80 + vN < v) (fr : Frame) (σ : State) (h : Seg61 t1 res txs fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA
      ((runInv g).map fun q => (q.1, fun fr' σ' => runVar q.1 args σ0 fr' σ' < v)) (fun _ => True) 200 61 fr σ := by
  obtain ⟨st1, h11, h1, h7, ht1, hst1, hlt, hci⟩ := h
  have hfw : ∀ σ', GrowsK σ σ' →
      σ'.heap t1 = some (.array (.cls "java.lang.String") txs) ∧
      σ'.heap st1 = some (.array (.prim .int) [.int 0, .int 0]) ∧ True := fun σ' hg =>
    ⟨by rw [(growsK_elim hg).2 _ (State.lt_next_of_heap ht1), ht1],
     by rw [(growsK_elim hg).2 _ (State.lt_next_of_heap hst1), hst1], trivial⟩
  have hs1 := str00_ne_10
  have hs2 := str04_ne_10
  by_cases hc : 0 < txs.length
  · have hcode : seqCode 0 0 txs.length = JStr.ofString "00" := by simp [seqCode, hc]
    have harr : seqStArr 0 0 txs.length = [.int 1, .int 0] := by simp [seqStArr, hc]
    refine bodyWP_cut_insert (callWPThin_mono _ _ 1) _ _ _ 69 (by rfl) (Seg69 st1) 100
      (by intro fr' σ' h; exact seg69 g args σ0 v st1 hv fr' σ' h) 100 61 fr σ ?_
    clear hv
    jvc [runCallees, runInv, Seg69, grows_split, keeps_split, fixStr_length]
  · have hcode : seqCode 0 0 txs.length = JStr.ofString "10" := by simp [seqCode, hc]
    have harr : seqStArr 0 0 txs.length = [.int 0, .int 1] := by simp [seqStArr, hc]
    clear hv
    jvc [runCallees, runInv, grows_split, keeps_split]

end EquivLean.Modernize.Cbstm03a.Java.Thin3
