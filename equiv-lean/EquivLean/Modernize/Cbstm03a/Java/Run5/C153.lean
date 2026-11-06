import EquivLean.Modernize.Cbstm03a.Java.Run5.Lem

/-!
# CBSTM03A → Java `run`: the paths from statement 153 (the account search of cross-reference record `j`)

From `label32` with `i#78 = i`: text `i` of `acctTexts` starting with the account id `cn` → `createStatement` and
the cards loop's head (`inv168`, card number 1, total 0); another text → back at 153 with `i + 1`; the texts
exhausted → `abend(res, "ERROR READING ACCTFILE", "23")` and `run` returns (the model's `xrefStep` errors).
One lemma per path, the facts the symbolic run needs as hypotheses, the rest folded in `Kept`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

section Paths

/- `jsimp`'s `List.take_succ` would spell the 11 characters of the substring out one by one, and the account id's
comparison with them would then split instead of being decided by the hypothesis about `List.take 11 s`. -/
attribute [-jsimp] List.take_succ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- Path 3: the texts exhausted, `abend`. -/
theorem p3 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh : Addr) (o : JOut)
    (i n4 : I32)
    (hK : Kept (ResAtL σ res ld ls lh o.disp o.stmt o.html o.ab ∧
      g.F = o.abend (jl "ERROR READING ACCTFILE") (jl "23")))
    (hf26 : fr.get 26 = some (.int i)) (hf28 : fr.get 28 = some (.int n4)) (hf38 : fr.get 38 = some .null)
    (hf7 : fr.get 7 = some (.ref res)) (hinitC : σ.initOf "Cbstm03a" = .done) (hge : n4.toInt ≤ i.toInt) :
    runWP g args σ0 153 fr σ := by
  unfold runWP
  jvc [runCallees, runInv, runSpecG, ite_nat_ne]
  · obtain ⟨hR, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, o.disp, o.stmt, o.html, resAtL_or hR (grows_trans (grows_alloc _ _) (grows_alloc _ _))⟩
  · exact ⟨_, σ.next, rfl, heap_alloc2_fst σ _ _⟩
  · exact ⟨_, σ.next + 1, rfl, heap_alloc2_snd σ _ _⟩
  · rename_i v σ' hA
    obtain ⟨hR, hF⟩ := Kept.elim hK
    have hR2 := resAtL_grows hR (grows_trans (grows_alloc σ (.str (JStr.ofString "ERROR READING ACCTFILE")))
      (grows_alloc _ (.str (JStr.ofString "23"))))
    have hA' := hA res ld ls lh o.disp o.stmt o.html
    rw [argText_alloc2_fst, argText_alloc2_snd] at hA'
    rw [hF]
    cases hab : o.ab <;> rw [hab] at hR2
    · obtain ⟨hv, hR', -⟩ := hA'.1 rfl hR2
      exact ⟨res, by rw [hv]; try rfl, ld, ls, lh, hR'⟩
    · obtain ⟨hv, hR', -⟩ := hA'.2 rfl hR2
      exact ⟨res, by rw [hv]; try rfl, ld, ls, lh, hR'⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- Path 2: text `i` does not start with the account id: back at 153 with `i + 1`. -/
theorem p2 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh : Addr) (L : LdSt)
    (o : JOut) (j : Nat) (crec : JStr) (t4 y xcn : Addr) (xs4 : List Value) (s aid : JStr) (i n4 : I32)
    (hK : Kept (XCtx g σ0 fr σ res ld ls lh o L (j + 1) ∧ j < g.T2.length ∧
      xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F ∧ XrecLocs σ fr (g.T2.getD j []) ∧ StrLoc σ fr 37 crec ∧
      custFind g.K3 g.T3 (sub (fixStr (g.T2.getD j []) 1000) 16 25) = some crec ∧
      (∀ k, k < i.toInt.toNat → sub (g.T4.getD k []) 0 11 ≠ sub (fixStr (g.T2.getD j []) 1000) 25 36) ∧
      sub (g.T4.getD i.toInt.toNat []) 0 11 ≠ sub (fixStr (g.T2.getD j []) 1000) 25 36 ∧
      n4.toInt = g.ars.length))
    (hf26 : fr.get 26 = some (.int i)) (hf28 : fr.get 28 = some (.int n4)) (hf38 : fr.get 38 = some .null)
    (hf7 : fr.get 7 = some (.ref res)) (hinitC : σ.initOf "Cbstm03a" = .done)
    (hf15 : fr.get 15 = some (.ref t4)) (ht4 : σ.heap t4 = some (.array (.cls "java.lang.String") xs4))
    (hi0 : 0 ≤ i.toInt) (hilt : i.toInt < (xs4.length : Int)) (hk : i.toInt.toNat < xs4.length)
    (hy : xs4[i.toInt.toNat]? = some (.ref y)) (hy' : xs4[i.toInt.toNat]'hk = .ref y)
    (hyh : σ.heap y = some (.str s)) (hsl : s.length = 300) (hf33 : fr.get 33 = some (.ref xcn))
    (hxcn : σ.heap xcn = some (.str aid)) (hlt : i.toInt < n4.toInt) (hnle : ¬ n4.toInt ≤ i.toInt)
    (hm1 : ¬ List.take 11 s = aid) (hm2 : ¬ aid = List.take 11 s) :
    runWP g args σ0 153 fr σ := by
  unfold runWP
  jvc [runCallees, runInv, runSpecG, ite_nat_ne]
  obtain ⟨hX, hj, hmodel, hxl, hcr, hcf, hall, hm, hn4⟩ := Kept.elim hK
  exact close153 hX hj hmodel hxl hcr hcf hall hm hi0 hlt hn4
    (fun k h4 h17 h21 h26 h35 h38 => by simp [Frame.get_setLocal, h4, h17, h21, h26, h35, h38])
    (by simpa [Frame.get_setLocal] using hf38) (get_setLocal_same _ _ _) (grows_alloc _ _) rfl rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- Path 1: text `i` starts with the account id: `createStatement`, the cards loop's head. -/
theorem p1 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh : Addr) (L : LdSt)
    (o : JOut) (j : Nat) (crec : JStr) (t4 y xcn xcr : Addr) (xs4 : List Value) (s aid : JStr) (i n4 : I32)
    (hK : Kept (XCtx g σ0 fr σ res ld ls lh o L (j + 1) ∧ j < g.T2.length ∧
      xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F ∧ XrecLocs σ fr (g.T2.getD j []) ∧
      custFind g.K3 g.T3 (sub (fixStr (g.T2.getD j []) 1000) 16 25) = some crec ∧
      acctFind g.T4 (sub (fixStr (g.T2.getD j []) 1000) 25 36) = some s ∧ crec.length = 500))
    (hf26 : fr.get 26 = some (.int i)) (hf28 : fr.get 28 = some (.int n4)) (hf38 : fr.get 38 = some .null)
    (hf7 : fr.get 7 = some (.ref res)) (hinitC : σ.initOf "Cbstm03a" = .done)
    (hf15 : fr.get 15 = some (.ref t4)) (ht4 : σ.heap t4 = some (.array (.cls "java.lang.String") xs4))
    (hi0 : 0 ≤ i.toInt) (hilt : i.toInt < (xs4.length : Int)) (hk : i.toInt.toNat < xs4.length)
    (hy : xs4[i.toInt.toNat]? = some (.ref y)) (hy' : xs4[i.toInt.toNat]'hk = .ref y)
    (hyh : σ.heap y = some (.str s)) (hsl : s.length = 300) (hf33 : fr.get 33 = some (.ref xcn))
    (hxcn : σ.heap xcn = some (.str aid)) (hlt : i.toInt < n4.toInt) (hnle : ¬ n4.toInt ≤ i.toInt)
    (hm : List.take 11 s = aid) (hf37 : fr.get 37 = some (.ref xcr)) (hxcr : σ.heap xcr = some (.str crec)) :
    runWP g args σ0 153 fr σ := by
  unfold runWP
  jvc [runCallees, runInv, runSpecG, ite_nat_ne]
  · obtain ⟨hX, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, o.disp, o.stmt, o.html, resAtL_or (xctx_resAtL hX) (grows_alloc _ _)⟩
  · obtain ⟨-, -, -, -, -, -, hcl⟩ := Kept.elim hK
    exact ⟨crec, ⟨xcr, rfl, (State.heap_alloc_of_lt (State.lt_next_of_heap hxcr) _).trans hxcr⟩, s,
      ⟨y, rfl, (State.heap_alloc_of_lt (State.lt_next_of_heap hyh) _).trans hyh⟩,
      by rw [hcl]; decide, by rw [hcl]; decide, by rw [hsl]; decide, by rw [hsl]; decide⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel, hxl, hcf, haf, -⟩ := Kept.elim hK
    have hRx := xctx_resAtL hX
    have hA' := hA res ld ls lh o.disp o.stmt o.html
    rw [argText_alloc_of hxcr, argText_alloc_of hyh] at hA'
    have key : ResAtL σ' res ld ls lh o.disp (o.stmt ++ (jCreateStatement crec s).1)
        (o.html ++ (jCreateStatement crec s).2) o.ab ∧ KeepsRes res ld ls lh σ σ' ∧
        σ'.inits = σ.inits ∧ σ'.statics = σ.statics := by
      cases hab : o.ab <;> rw [hab] at hRx
      · obtain ⟨-, h1, h2, h3, h4⟩ := hA'.1 rfl (resAtL_grows hRx (grows_alloc _ _))
        exact ⟨h1, keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) h2, h3, h4⟩
      · obtain ⟨-, h1, h2, h3, h4⟩ := hA'.2 rfl (resAtL_grows hRx (grows_alloc _ _))
        exact ⟨h1, keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) h2, h3, h4⟩
    obtain ⟨hR', hk', hi', hs'⟩ := key
    exact close168 hX hj hmodel hxl hcf haf
      (fun k h4 h17 h21 h26 h35 h38 => by simp [Frame.get_setLocal, h4, h17, h21, h26, h35, h38])
      (get_setLocal_same _ _ _) ((get_setLocal_of_ne _ _ (by decide)).trans (get_setLocal_same _ _ _))
      hk' hR' hi' hs'

end Paths

end EquivLean.Modernize.Cbstm03a.Java.Seg5

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg5

/-- **The paths from statement 153** (the account search of record `j`). -/
theorem run_cut153_vc (g : RunG) : RunCutVC g 153 inv153 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨res, ld, ls, lh, L, o, j, i, crec, hX, hj, hmodel, hxl, hcr, hcf, h38, h26, hi0, hiA, hall⟩ := hI
  have hR := xctx_resAtL hX
  have hX' := hX
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, ⟨-, -, -, -, hf7, -, -, -, -, -, -, hinits, -⟩,
    ⟨-, -, -, -, hf15, -, ⟨n4, hf28, hn4⟩, -, -, -, -, hT4, -, -, -, -, -⟩, -⟩ := hX'
  have hinitC : σ.initOf "Cbstm03a" = .done := by
    rw [State.initOf_eq_of_inits hinits]; exact hpre.2.2.2.2.2.1.1
  obtain ⟨xs4, hxs4, hxs4l, hF4⟩ := textsAt_get hT4
  have hT4l : g.T4.length = g.ars.length := by simp [RunG.T4]
  by_cases hge : n4.toInt ≤ i.toInt
  · have haf : acctFind g.T4 (sub (fixStr (g.T2.getD j []) 1000) 25 36) = none :=
      acctFind_none (fun k hk => hall k (by omega))
    exact p3 g args σ0 fr σ res ld ls lh o i n4 (Kept.intro ⟨hR, model_abend hj hmodel hcf haf⟩) h26 hf28 h38 hf7
      hinitC hge
  · have hlt : i.toInt < n4.toInt := by omega
    have hiT : i.toInt.toNat < g.T4.length := by omega
    obtain ⟨y, hy, hyh⟩ := forall2_jstr_get hF4 _ hiT
    have hk : i.toInt.toNat < xs4.length := by omega
    have hilt : i.toInt < (xs4.length : Int) := by omega
    have hy' : xs4[i.toInt.toNat]'hk = .ref y := by
      rw [List.getElem?_eq_getElem hk] at hy; exact Option.some.inj hy
    have hsl : (g.T4.getD i.toInt.toNat []).length = 300 := T4_len g hiT
    obtain ⟨xcn, hf33, hxcn⟩ := hxl.2.2
    by_cases hm : sub (g.T4.getD i.toInt.toNat []) 0 11 = sub (fixStr (g.T2.getD j []) 1000) 25 36
    · have haf := acctFind_of_prefix hiT hm hall
      have hcl := crec_len hcf
      obtain ⟨xcr, hf37, hxcr⟩ := hcr
      exact p1 g args σ0 fr σ res ld ls lh L o j crec t4 y xcn xcr xs4 _ _ i n4
        (Kept.intro ⟨hX, hj, hmodel, hxl, hcf, haf, hcl⟩) h26 hf28 h38 hf7 hinitC hf15 hxs4 hi0 hilt hk hy hy'
        hyh hsl hf33 hxcn hlt hge hm hf37 hxcr
    · exact p2 g args σ0 fr σ res ld ls lh L o j crec t4 y xcn xs4 _ _ i n4
        (Kept.intro ⟨hX, hj, hmodel, hxl, hcr, hcf, hall, hm, hn4⟩) h26 hf28 h38 hf7 hinitC hf15 hxs4 hi0 hilt hk
        hy hy' hyh hsl hf33 hxcn hlt hge hm (fun h => hm h.symm)

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut153_vc
