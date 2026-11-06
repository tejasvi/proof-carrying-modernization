import EquivLean.Modernize.Cbstm03a.Java.Thin3.Lem

/-!
# CBSTM03A → Java: `run`'s thin paths from cut point 80, from statement 93 on

`Thin3.Seg93` (statement 93, the first `memWrite`): the locals the rest reads, the slots array unchanged and every
string kept (`Thin3.slotsAt_mono`), `trnxTexts`, `trnxSt` = `{i1, 0}`. The three `memWrite`s keep `trnxTexts` and
`trnxSt`; `seqRead` answers `"00"` (records left: `trnxSt` = `{i1 + 1, 0}`, then `fix` of record `i1`, split again
at statement 107, `Thin3.Seg107`, with the record text generalized, back to cut point 80) or `"10"` (the load ends:
`setTrct`, a new `xrefSt` = `{0, 0}`, cut point 117).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space heap_grows GrowsK
  growsK_elim grows_split fixStr_length)

attribute [-simp] List.reduceReplicate

-- `jvc` destructures every hypothesis whose head unfolds to `∃`/`∧`: a `SlotsAt` fact kept folded is what
-- `memWrite`'s postcondition premise matches.
attribute [local irreducible] EquivLean.Modernize.Cbstm03a.Java.SlotsAt

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

theorem R1_getD_length (g : RunG) {k : Nat} (h : k < g.R1.length) : (g.R1.getD k []).length = 350 := by
  rw [List.getD_eq_getElem _ _ h]
  simp [RunG.R1, recOf, sub, fixStr_length]

theorem ofNat32_toNat {j : Nat} (h : j < 2147483648) : (BitVec.ofNat 32 j).toNat = j := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem ofNat32_toInt {j : Nat} (h : j < 2147483648) : (BitVec.ofNat 32 j).toInt = j := by
  rw [BitVec.toInt_eq_toNat_cond, ofNat32_toNat h]; split <;> omega

theorem toInt_succ32 {x : I32} (h0 : 0 ≤ x.toInt) (h1 : x.toInt < 2147483647) :
    (x + 1).toInt = x.toInt + 1 := by
  rw [BitVec.toInt_add]
  have e : (1 : I32).toInt = 1 := by decide
  rw [e]
  exact Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)

theorem bmod32_succ {x : I32} (h0 : 0 ≤ x.toInt) (h1 : x.toInt < 2147483647) :
    (x.toInt + 1).bmod 4294967296 = x.toInt + 1 :=
  Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)

theorem s00_ne_10 : ¬ JStr.ofString "00" = JStr.ofString "10" := by decide +kernel

/-- Statement 93 of the paths from 80 (before the first `memWrite`): the locals the rest reads, the slots array
unchanged and every string of `σS` kept, `trnxTexts` holding `txs`, `trnxSt` = `{i1, 0}`. -/
def Seg93 (σS : State) (mem t1 st1 trct res : Addr) (txs : List Value) (i1 : I32) (fr : Frame) (σ : State) :
    Prop :=
  fr.get 16 = some (.ref mem) ∧ fr.get 11 = some (.ref t1) ∧ fr.get 1 = some (.ref st1) ∧
  fr.get 24 = some (.ref trct) ∧ fr.get 7 = some (.ref res) ∧
  (∃ c : I64, fr.get 19 = some (.long c)) ∧ (∃ c : I64, fr.get 18 = some (.long c)) ∧
  (∃ c : I64, fr.get 17 = some (.long c)) ∧
  (∃ x s, fr.get 36 = some (.ref x) ∧ σ.heap x = some (.str s)) ∧
  (∃ x s, fr.get 34 = some (.ref x) ∧ σ.heap x = some (.str s)) ∧
  (∃ x s, fr.get 33 = some (.ref x) ∧ σ.heap x = some (.str s)) ∧
  σ.heap t1 = some (.array (.cls "java.lang.String") txs) ∧
  σ.heap st1 = some (.array (.prim .int) [.int i1, .int 0]) ∧
  (∃ tv, σ.heap trct = some (.array (.prim .long) tv)) ∧
  σ.heap mem = σS.heap mem ∧
  (∀ x s, σS.heap x = some (.str s) → x ≠ trct → σ.heap x = some (.str s)) ∧ σ.initOf "Cbstm03a" = .done

/-- Statement 107 with records left (after `fix`): `cn` a string of 1000 characters, `trnxSt` = `{i1 + 1, 0}`. -/
def Seg107 (st1 : Addr) (i1 : I32) (fr : Frame) (σ : State) : Prop :=
  (∃ x s, fr.get 33 = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length = 1000) ∧
  fr.get 1 = some (.ref st1) ∧ σ.heap st1 = some (.array (.prim .int) [.int (i1 + 1), .int 0]) ∧
  σ.initOf "Cbstm03a" = .done

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 3000000 in
/-- From statement 107: the record's first 350 characters, cut point 80 with `trnxSt[0] = i1 + 1`. -/
theorem seg107 (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (st1 : Addr) (i1 : I32)
    (hi2 : (i1 + 1).toInt = i1.toInt + 1) (hi3 : (i1.toInt + 1).bmod 4294967296 = i1.toInt + 1)
    (hv : vX80 + ((vN : Int) - i1.toInt).toNat ≤ v) (fr : Frame) (σ : State) (h : Seg107 st1 i1 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA
      ((runInv g).map fun q => (q.1, fun fr' σ' => runVar q.1 args σ0 fr' σ' < v)) (fun _ => True) 100 107 fr σ := by
  obtain ⟨⟨x, s, h33, hx, hs⟩, h1, hst1, hci⟩ := h
  simp only [vX80, vM, vC3, vC4, vK, vN] at hv
  jvc [runCallees, runInv, runVar, arr0, vN, vM, vC3, vC4, vK, vX80]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
/-- From statement 93: three `memWrite`s, `seqRead`; records left: `fix` of record `i1`, statement 107; none:
`setTrct`, cut point 117 with a new `xrefSt`. -/
theorem seg93 (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (σS : State) (mem t1 st1 trct res : Addr)
    (txs : List Value) (i1 : I32) (m : Nat → JChar) (hS : SlotsAt σS mem m) (tvS : List Value)
    (htrS : σS.heap trct = some (.array (.prim .long) tvS)) (hl : txs.length < 2147483648)
    (hi0 : 0 ≤ i1.toInt) (ht1m : t1 < mem) (hmt : mem < trct) (hts : trct < st1)
    (hv : vX80 + ((vN : Int) - i1.toInt).toNat ≤ v) (fr : Frame) (σ : State)
    (h : Seg93 σS mem t1 st1 trct res txs i1 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA
      ((runInv g).map fun q => (q.1, fun fr' σ' => runVar q.1 args σ0 fr' σ' < v)) (fun _ => True) 200 93 fr σ := by
  obtain ⟨h16, h11, h1, h24, h7, ⟨c19, h19⟩, ⟨cr, h18⟩, ⟨tr, h17⟩, ⟨xt, tt, h36, hxt⟩, ⟨xc, tc, h34, hxc⟩,
    ⟨xn, tn, h33, hxn⟩, ht1, hst1, ⟨tv, htr⟩, hmem, hsm, hci⟩ := h
  have hsm' : StrMono σS σ := fun x s hx => hsm x s hx (ne_of_heap hx htrS (by simp))
  have hS' : SlotsAt σ mem m := slotsAt_mono hS hmem hsm'
  obtain ⟨vs0, hmemh⟩ := slotsAt_heap hS'
  have hxcm : xc ≠ mem := ne_of_heap hxc hmemh (by simp)
  have hxnm : xn ≠ mem := ne_of_heap hxn hmemh (by simp)
  have hxtm : xt ≠ mem := ne_of_heap hxt hmemh (by simp)
  clear hS hmem hsm hsm' htrS
  -- the facts the later calls' premises need, about the states after the `memWrite`s (`jvc` instantiates these
  -- with the callees' `KeepsK`): a premise `σ'.heap x = …` with `x` bound is never rewritten by `simp`
  have ht1m' : t1 ≠ mem := Nat.ne_of_lt ht1m
  have hst1m : st1 ≠ mem := Nat.ne_of_gt (Nat.lt_trans hmt hts)
  have htrm : trct ≠ mem := Nat.ne_of_gt hmt
  have kp : ∀ {σ1 σ2 : State} {y : Addr} {o : Obj}, KeepsK (fun x => x = mem) σ1 σ2 → σ1.heap y = some o →
      y ≠ mem → σ2.heap y = some o := fun hk hy hne => by
    rw [(keepsK_elim hk).2 _ (State.lt_next_of_heap hy) hne, hy]
  have hfw1 : ∀ σ1, KeepsK (fun x => x = mem) σ σ1 →
      σ1.heap xc = some (.str tc) ∧ σ1.heap xn = some (.str tn) ∧ True := fun σ1 k1 =>
    ⟨kp k1 hxc hxcm, kp k1 hxn hxnm, trivial⟩
  have hfw2 : ∀ σ1 σ2, KeepsK (fun x => x = mem) σ σ1 → KeepsK (fun x => x = mem) σ1 σ2 →
      σ2.heap xn = some (.str tn) ∧ True := fun σ1 σ2 k1 k2 =>
    ⟨kp k2 (kp k1 hxn hxnm) hxnm, trivial⟩
  have hfw3 : ∀ σ1 σ2 σ3, KeepsK (fun x => x = mem) σ σ1 → KeepsK (fun x => x = mem) σ1 σ2 →
      KeepsK (fun x => x = mem) σ2 σ3 →
      σ3.heap t1 = some (.array (.cls "java.lang.String") txs) ∧
      σ3.heap st1 = some (.array (.prim .int) [.int i1, .int 0]) ∧
      σ3.heap trct = some (.array (.prim .long) tv) ∧ True := fun σ1 σ2 σ3 k1 k2 k3 =>
    ⟨kp k3 (kp k2 (kp k1 ht1 ht1m') ht1m') ht1m', kp k3 (kp k2 (kp k1 hst1 hst1m) hst1m) hst1m,
     kp k3 (kp k2 (kp k1 htr htrm) htrm) htrm, trivial⟩
  clear kp
  have hs1 := s00_ne_10
  by_cases hc : i1.toInt < txs.length
  · have hcode : seqCode i1 0 txs.length = JStr.ofString "00" := by simp [seqCode, hc]
    have harr : seqStArr i1 0 txs.length = [.int (i1 + 1), .int 0] := by simp [seqStArr, hc]
    have hi2 : (i1 + 1).toInt = i1.toInt + 1 := toInt_succ32 hi0 (by omega)
    have hi3 : (i1.toInt + 1).bmod 4294967296 = i1.toInt + 1 := bmod32_succ hi0 (by omega)
    refine bodyWP_cut_insert (callWPThin_mono _ _ 1) _ _ _ 107 (by rfl) (Seg107 st1 i1) 100
      (by intro fr' σ' h; exact seg107 g args σ0 v st1 i1 hi2 hi3 hv fr' σ' h) 100 93 fr σ ?_
    clear hv hi2 hi3
    jvc [runCallees, runInv, Seg107, grows_split, keeps_split, fixStr_length]
  · have hcode : seqCode i1 0 txs.length = JStr.ofString "10" := by simp [seqCode, hc]
    have harr : seqStArr i1 0 txs.length = [.int i1, .int 1] := by simp [seqStArr, hc]
    simp only [vX80, vM, vC3, vC4, vK, vN] at hv
    jvc [runCallees, runInv, runVar, arr0, vN, vM, vC3, vC4, vK, vX80, seqCode, seqStArr, grows_split, keeps_split, rep2]

end EquivLean.Modernize.Cbstm03a.Java.Thin3
