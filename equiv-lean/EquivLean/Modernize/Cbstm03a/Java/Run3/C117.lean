import EquivLean.Modernize.Cbstm03a.Java.Run3.Frame2

/-!
# CBSTM03A → Java, `run`: the paths from cut point 117 (the cross-reference loop)

`spaces(1000)`, `seqRead(xrefTexts, xrefSt)`: status `"00"` (record `j` left) reads `xrefTexts[j]`, `fix`es it to
1000 characters and takes its card number, customer id and account id (`inv140`); status `"10"` (all read) ends the
loop and returns the `Result` holding `g.F`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim fixStr_length)
open EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java.Seg3

attribute [local simp high] rep1000
attribute [local simp high] take_eq_takeK
attribute [local irreducible] fixStr

theorem ofNat32_toNat {j : Nat} (h : j < 2147483648) : (BitVec.ofNat 32 j).toNat = j := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem ofNat32_toInt {j : Nat} (h : j < 2147483648) : (BitVec.ofNat 32 j).toInt = j := by
  rw [BitVec.toInt_eq_toNat_cond, ofNat32_toNat h]; split <;> omega

theorem xrs_len_lt {g : RunG} {args : List Value} {σ0 : State} (hpre : RunPre g args σ0) :
    g.T2.length < 2147483648 := by
  obtain ⟨-, -, hR2, -⟩ := hpre
  simpa [RunG.T2] using recsAt_len hR2

-- 117, a record left: up to `inv140`.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem c117_read (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame)
    (σ : State) (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat)
    (hX : XCtx g σ0 fr σ res ld ls lh o L j) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F) :
    runWP g args σ0 117 fr σ := by
  have hXk := Kp.intro hX
  have hmk := Kp.intro hmodel
  clear hmodel
  have hj31 : j < 2147483648 := Nat.lt_trans hj (xrs_len_lt hpre)
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, -, hf2, hst2, h4m, hmt, hts, hf5, hf3, -, -⟩ := hX
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hinits, -⟩ := hB
  obtain ⟨-, hf12, -, -, -, -, -, -, hT2, -, -, -, -, -, h23, h34, h45⟩ := hT
  obtain ⟨xs2, hxs2, hxs2l, hF2⟩ := textsAt_get hT2
  clear hT2
  have hinitC : σ.initOf "Cbstm03a" = .done := initC_of hpre hinits
  have hlen2 : xs2.length < 2147483648 := by rw [hxs2l]; exact xrs_len_lt hpre
  clear hinits hpre
  obtain ⟨y2, hy2, hy2h⟩ := forall2_jstr_get hF2 j hj
  clear hF2
  have hy2len : (g.T2.getD j []).length = 50 := T2_len g hj
  generalize htx : g.T2.getD j [] = tx at hy2h hy2len
  have htxk := Kp.intro htx
  clear htx
  have ht2lt : t2 < σ.next := State.lt_next_of_heap hxs2
  have hst2lt : st2 < σ.next := State.lt_next_of_heap hst2
  have hy2lt : y2 < σ.next := State.lt_next_of_heap hy2h
  have ht2st2 : t2 ≠ st2 := Nat.ne_of_lt (Nat.lt_trans h23 (Nat.lt_trans h34 (Nat.lt_trans h45
    (Nat.lt_trans h4m (Nat.lt_trans hmt hts)))))
  have hy2st2 : y2 ≠ st2 := by rintro rfl; rw [hst2] at hy2h; cases hy2h
  clear h23 h34 h45 h4m hmt hts
  generalize hij : (BitVec.ofNat 32 j : I32) = ij at hst2
  have hijn : ij.toNat = j := by rw [← hij]; exact ofNat32_toNat hj31
  have hiji : ij.toInt = j := by rw [← hij]; exact ofNat32_toInt hj31
  have hijk := Kp.intro hij
  clear hij
  have hij0 : 0 ≤ ij.toInt := by rw [hiji]; omega
  have hlt : ij.toInt < (xs2.length : Int) := by rw [hiji, hxs2l]; exact_mod_cast hj
  have hb : ij.toInt.toNat < xs2.length := by omega
  have hy2e : xs2[ij.toInt.toNat]'hb = .ref y2 := by
    have h := List.getElem?_eq_some_iff.mp
      (show xs2[ij.toInt.toNat]? = some (.ref y2) by rw [hiji, Int.toNat_natCast]; exact hy2)
    exact h.2
  clear hy2 hxs2l hijn hiji
  -- the heap facts `seqRead`'s postcondition needs, at the state after `spaces`
  have hfw : ∀ σ', GrowsK σ σ' →
      σ'.heap t2 = some (.array (.cls "java.lang.String") xs2) ∧
      σ'.heap st2 = some (.array (.prim .int) [.int ij, .int 0]) ∧ True := fun σ' hg =>
    ⟨by rw [(growsK_elim hg).2 _ ht2lt, hxs2], by rw [(growsK_elim hg).2 _ hst2lt, hst2], trivial⟩
  unfold runWP
  jvc [runCallees, runInv, spacesSig, fixSig, seqReadSig, seqCode, seqStArr, grows_split, keeps_split, StrOk,
    argText, fixStr_length, ite_nat_ne]
  -- the cut 140
  have htx := Kp.elim htxk
  subst htx
  try simp only [hlt, ↓reduceIte] at *
  have e1 : BitVec.ofNat 32 (j + 1) = ij + 1#32 := by rw [← Kp.elim hijk, BitVec.ofNat_add_ofNat]
  refine ⟨res, ld, ls, lh, L, o, j, 0, ?_, hj, Kp.elim hmk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine xctx_keeps_st2 (Kp.elim hXk) hf2 (by seg3_keeps_tac) ?_ (by seg3_fr_tac) ?_ ?_
    · rw [e1]
      refine heap_alloc_eq ?_ (heap_alloc_eq ?_ (heap_alloc_eq ?_ (heap_growsK_eq (by assumption) ?_
        (heap_alloc_eq ?_ ‹_›))))
      all_goals jdisch
    · simp only [State.alloc_inits]; assumption
    · simp only [State.alloc_statics]; assumption
  · refine ⟨?_, ?_, ?_⟩
    · simp (config := {decide := true}) only [StrLoc, Frame.get_setLocal, ↓reduceIte, Option.some.injEq,
        Value.ref.injEq, exists_eq_left']
      refine heap_alloc_eq ?_ (heap_alloc_eq ?_ (heap_alloc_at rfl ?_))
      · jdisch
      · jdisch
      · rw [← take_eq_takeK]; rfl
    · simp (config := {decide := true}) only [StrLoc, Frame.get_setLocal, ↓reduceIte, Option.some.injEq,
        Value.ref.injEq, exists_eq_left']
      refine heap_alloc_eq ?_ (heap_alloc_at (State.next_alloc _ _).symm ?_)
      · jdisch
      · rw [← take_eq_takeK]; rfl
    · simp (config := {decide := true}) only [StrLoc, Frame.get_setLocal, ↓reduceIte, Option.some.injEq,
        Value.ref.injEq, exists_eq_left']
      refine heap_alloc_at (by simp only [State.next_alloc]) ?_
      rw [← take_eq_takeK]; rfl
  · simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte]
  · simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte]
    try rfl
  · decide
  · simp
  · intro k hk; simp at hk

-- 117, all records read: the loop ends, `run` returns the `Result`.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem c117_eof (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame)
    (σ : State) (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat)
    (hX : XCtx g σ0 fr σ res ld ls lh o L j) (hj : j = g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F) :
    runWP g args σ0 117 fr σ := by
  have hXk := Kp.intro hX
  have hmk := Kp.intro hmodel
  clear hmodel
  have hj31 : j < 2147483648 := by rw [hj]; exact xrs_len_lt hpre
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, -, hf2, hst2, h4m, hmt, hts, hf5, hf3, -, -⟩ := hX
  obtain ⟨-, -, -, -, hf7, -, -, -, -, -, -, hinits, -⟩ := hB
  obtain ⟨-, hf12, -, -, -, -, -, -, hT2, -, -, -, -, -, h23, h34, h45⟩ := hT
  obtain ⟨xs2, hxs2, hxs2l, -⟩ := textsAt_get hT2
  clear hT2
  have hinitC : σ.initOf "Cbstm03a" = .done := initC_of hpre hinits
  have hlen2 : xs2.length < 2147483648 := by rw [hxs2l]; exact xrs_len_lt hpre
  clear hinits hpre
  have ht2lt : t2 < σ.next := State.lt_next_of_heap hxs2
  have hst2lt : st2 < σ.next := State.lt_next_of_heap hst2
  have ht2st2 : t2 ≠ st2 := Nat.ne_of_lt (Nat.lt_trans h23 (Nat.lt_trans h34 (Nat.lt_trans h45
    (Nat.lt_trans h4m (Nat.lt_trans hmt hts)))))
  clear h23 h34 h45 h4m hmt hts
  generalize hij : (BitVec.ofNat 32 j : I32) = ij at hst2
  have hiji : ij.toInt = j := by rw [← hij]; exact ofNat32_toInt hj31
  have hijk := Kp.intro hij
  clear hij
  have hge : ¬ ij.toInt < (xs2.length : Int) := by rw [hiji, hxs2l, ← hj]; omega
  clear hxs2l hiji
  have hfw : ∀ σ', GrowsK σ σ' →
      σ'.heap t2 = some (.array (.cls "java.lang.String") xs2) ∧
      σ'.heap st2 = some (.array (.prim .int) [.int ij, .int 0]) ∧ True := fun σ' hg =>
    ⟨by rw [(growsK_elim hg).2 _ ht2lt, hxs2], by rw [(growsK_elim hg).2 _ hst2lt, hst2], trivial⟩
  unfold runWP
  jvc [runCallees, runInv, spacesSig, fixSig, seqReadSig, seqCode, seqStArr, grows_split, keeps_split, StrOk,
    argText, fixStr_length, ite_nat_ne]
  -- the return
  have hm := Kp.elim hmk
  (try rw [hj] at hm)
  rw [List.drop_length] at hm
  rw [← hm]
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, _, _, _, _, hres, _⟩, _⟩ := Kp.elim hXk
  exact ⟨ld, ls, lh, resAtL_on (keepsOn_of_keeps (by seg3_keeps_tac) hst2) notIntArr_str notIntArr_list
    notIntArr_plain hres⟩

end EquivLean.Modernize.Cbstm03a.Java.Seg3

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg3 in
theorem run_cut117_vc (g : RunG) : RunCutVC g 117 inv117 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨res, ld, ls, lh, L, o, j, hX, hjle, hm⟩ := hI
  rcases Nat.lt_or_ge j g.T2.length with hj | hj
  · exact c117_read g args σ0 hpre fr σ res ld ls lh L o j hX hj hm
  · exact c117_eof g args σ0 hpre fr σ res ld ls lh L o j hX (Nat.le_antisymm hjle hj) hm

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut117_vc
