import EquivLean.Modernize.Cbstm03a.Java.Run3.Frame2

/-!
# CBSTM03A → Java, `run`: the paths from cut point 140 (the search of the customer keys)

Key `i` equal to the customer id: `custRec = custTexts[i]`, on to the account search (`inv153`); different: the next
key (`inv140`); keys exhausted: `abend(res, "ERROR READING CUSTFILE", "23")` and return.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim fixStr_length)
open EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java.Seg3

attribute [local simp high] rep1000
attribute [local simp high] take_eq_takeK
attribute [local irreducible] fixStr
attribute [local irreducible] ResAtL


-- 140, key `i` equal to the customer id: on to 153.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem c140_match (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame)
    (σ : State) (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat) (i : I32)
    (hX : XCtx g σ0 fr σ res ld ls lh o L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F) (hx : XrecLocs σ fr (g.T2.getD j []))
    (h37 : fr.get 37 = some .null) (h26 : fr.get 26 = some (.int i)) (hi0 : 0 ≤ i.toInt)
    (hlt : i.toInt < g.crs.length)
    (hne : ∀ k, k < i.toInt.toNat → g.K3.getD k [] ≠ sub (fixStr (g.T2.getD j []) 1000) 16 25)
    (hm : g.K3.getD i.toInt.toNat [] = sub (fixStr (g.T2.getD j []) 1000) 16 25) :
    runWP g args σ0 140 fr σ := by
  have hXk := Kp.intro hX
  have hmk := Kp.intro hmodel
  have hxk := Kp.intro hx
  have hnek := Kp.intro hne
  have hmk2 := Kp.intro hm
  clear hmodel hne
  have hK3l : g.K3.length = g.T3.length := by simp [RunG.K3]
  have hT3l : g.T3.length = g.crs.length := by simp [RunG.T3]
  have hik : i.toInt.toNat < g.K3.length := by omega
  have hit : i.toInt.toNat < g.T3.length := by omega
  have hlkk := Kp.intro (And.intro hK3l hik)
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, -, -, -, -, -, -, -, -, -, -⟩ := hX
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hinits, -⟩ := hB
  obtain ⟨-, -, hf13, hf14, -, ⟨n3, hf27, hn3⟩, -, -, -, hT3k, hT3, -, -, -, -, -, -⟩ := hT
  obtain ⟨xs3k, hxs3k, hxs3kl, hF3k⟩ := textsAt_get hT3k
  obtain ⟨xs3, hxs3, hxs3l, hF3⟩ := textsAt_get hT3
  obtain ⟨-, ⟨x34, hf34, hx34⟩, -⟩ := hx
  clear hT3k hT3
  have hinitC : σ.initOf "Cbstm03a" = .done := initC_of hpre hinits
  clear hinits hpre
  obtain ⟨yk, hyk, hykh⟩ := forall2_jstr_get hF3k _ hik
  obtain ⟨yc, hyc, hych⟩ := forall2_jstr_get hF3 _ hit
  clear hF3k hF3
  have hbk : i.toInt.toNat < xs3k.length := by omega
  have hbc : i.toInt.toNat < xs3.length := by omega
  have hyke : xs3k[i.toInt.toNat]'hbk = .ref yk := (List.getElem?_eq_some_iff.mp hyk).2
  have hyce : xs3[i.toInt.toNat]'hbc = .ref yc := (List.getElem?_eq_some_iff.mp hyc).2
  clear hyk hyc
  have hcnt : i.toInt < n3.toInt := by omega
  have hilt : i.toInt < (xs3k.length : Int) := by omega
  have hilt' : i.toInt < (xs3.length : Int) := by omega
  clear hxs3kl hxs3l hn3 hK3l hT3l hik hit hlt
  generalize hkk : g.K3.getD i.toInt.toNat [] = kk at hykh hm
  generalize hcid : sub (fixStr (g.T2.getD j []) 1000) 16 25 = cid at hx34 hm
  clear hkk hcid
  subst hm
  have hychk := Kp.intro hych
  clear hych
  unfold runWP
  jvc [runCallees, runInv, ite_nat_ne]
  -- the cut 153
  have hych := Kp.elim hychk
  obtain ⟨hK3l, hik⟩ := Kp.elim hlkk
  refine ⟨res, ld, ls, lh, L, o, j, 0, g.T3.getD i.toInt.toNat [], xctx_frame (Kp.elim hXk) (by seg3_fr_tac), hj,
    Kp.elim hmk, ?_, ?_, custFind_some hK3l hik (Kp.elim hnek) (Kp.elim hmk2), ?_, ?_, by decide, by simp, ?_⟩
  · exact xrecLocs_frame (Kp.elim hxk) (by simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte])
      (by simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte])
      (by simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte])
  · exact ⟨yc, by simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte], hych⟩
  · simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte]
  · simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte]
    try rfl
  · intro k hk; simp at hk

-- 140, key `i` different from the customer id: the next key.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem c140_miss (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame)
    (σ : State) (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat) (i : I32)
    (hX : XCtx g σ0 fr σ res ld ls lh o L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F) (hx : XrecLocs σ fr (g.T2.getD j []))
    (h37 : fr.get 37 = some .null) (h26 : fr.get 26 = some (.int i)) (hi0 : 0 ≤ i.toInt)
    (hlt : i.toInt < g.crs.length)
    (hne : ∀ k, k < i.toInt.toNat → g.K3.getD k [] ≠ sub (fixStr (g.T2.getD j []) 1000) 16 25)
    (hm : g.K3.getD i.toInt.toNat [] ≠ sub (fixStr (g.T2.getD j []) 1000) 16 25) :
    runWP g args σ0 140 fr σ := by
  have hXk := Kp.intro hX
  have hmk := Kp.intro hmodel
  have hxk := Kp.intro hx
  have hnek := Kp.intro hne
  have hmk2 := Kp.intro hm
  have h37k := Kp.intro h37
  have hcl := crs_len_lt hpre
  have hi1 : (i + 1).toInt = i.toInt + 1 := toInt_add_one32 hi0 (by omega)
  have hi1k := Kp.intro (And.intro hi1 (And.intro hi0 hlt))
  clear hmodel hne hi1
  have hK3l : g.K3.length = g.crs.length := by simp [RunG.K3, RunG.T3]
  have hik : i.toInt.toNat < g.K3.length := by omega
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, -, -, -, -, -, -, -, -, -, -⟩ := hX
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hinits, -⟩ := hB
  obtain ⟨-, -, hf13, -, -, ⟨n3, hf27, hn3⟩, -, -, -, hT3k, -, -, -, -, -, -, -⟩ := hT
  obtain ⟨xs3k, hxs3k, hxs3kl, hF3k⟩ := textsAt_get hT3k
  obtain ⟨-, ⟨x34, hf34, hx34⟩, -⟩ := hx
  clear hT3k
  have hinitC : σ.initOf "Cbstm03a" = .done := initC_of hpre hinits
  clear hinits hpre
  obtain ⟨yk, hyk, hykh⟩ := forall2_jstr_get hF3k _ hik
  clear hF3k
  have hbk : i.toInt.toNat < xs3k.length := by omega
  have hyke : xs3k[i.toInt.toNat]'hbk = .ref yk := (List.getElem?_eq_some_iff.mp hyk).2
  clear hyk
  have hcnt : i.toInt < n3.toInt := by omega
  have hilt : i.toInt < (xs3k.length : Int) := by omega
  clear hxs3kl hn3 hK3l hik hlt hcl
  generalize hkk : g.K3.getD i.toInt.toNat [] = kk at hykh hm
  generalize hcid : sub (fixStr (g.T2.getD j []) 1000) 16 25 = cid at hx34 hm
  clear hkk hcid
  have hm2 : ¬ cid = kk := fun e => hm e.symm
  unfold runWP
  jvc [runCallees, runInv, ite_nat_ne]
  -- the cut 140
  obtain ⟨hi1, hi0', hlt'⟩ := Kp.elim hi1k
  refine ⟨res, ld, ls, lh, L, o, j, i + 1, xctx_frame (Kp.elim hXk) (by seg3_fr_tac), hj, Kp.elim hmk, ?_, ?_, ?_,
    by omega, by omega, ?_⟩
  · exact xrecLocs_frame (Kp.elim hxk) (by simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte])
      (by simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte])
      (by simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte])
  · simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte]; exact Kp.elim h37k
  · simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte]
    try rfl
  · intro k hk
    rw [hi1] at hk
    rcases Nat.lt_or_ge k i.toInt.toNat with hk' | hk'
    · exact Kp.elim hnek k hk'
    · have : k = i.toInt.toNat := by omega
      rw [this]; exact Kp.elim hmk2

-- 140, keys exhausted: `abend(res, "ERROR READING CUSTFILE", "23")`, return.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem c140_none (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame)
    (σ : State) (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat) (i : I32)
    (hX : XCtx g σ0 fr σ res ld ls lh o L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F)
    (h37 : fr.get 37 = some .null) (h26 : fr.get 26 = some (.int i))
    (hge : (g.crs.length : Int) ≤ i.toInt)
    (hne : ∀ k, k < i.toInt.toNat → g.K3.getD k [] ≠ sub (fixStr (g.T2.getD j []) 1000) 16 25) :
    runWP g args σ0 140 fr σ := by
  have hK3l : g.K3.length = g.T3.length := by simp [RunG.K3]
  have hF : g.F = o.abend (jl "ERROR READING CUSTFILE") (jl "23") :=
    model_cust_none hj hmodel (custFind_none hK3l (fun m hm => hne m (by simp [RunG.K3, RunG.T3] at hm; omega)))
  have hFk := Kp.intro hF
  clear hmodel hne hK3l hF
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, -, -, -, -, -, -, -, -, -, -⟩ := hX
  obtain ⟨-, -, -, -, hf7, hres, -, -, -, -, -, hinits, -⟩ := hB
  obtain ⟨-, -, -, -, -, ⟨n3, hf27, hn3⟩, -, -, -, -, -, -, -, -, -, -, -⟩ := hT
  have hinitC : σ.initOf "Cbstm03a" = .done := initC_of hpre hinits
  clear hinits hpre
  have hcnt : n3.toInt ≤ i.toInt := by omega
  clear hn3 hge
  have hRc := resAtL_alloc (ob := .str (JStr.ofString "23"))
    (resAtL_alloc (ob := .str (JStr.ofString "ERROR READING CUSTFILE")) hres)
  clear hres
  cases hab : o.ab
  · rw [hab] at hRc
    unfold runWP
    jvc [runCallees, runInv, abendSig, JStrAt, argText, ite_nat_ne]
    have hpost := ‹∀ (res_1 ld ls lh : Addr) (disp st ht : List JStr), _›
    obtain ⟨hv, hR, -⟩ := (hpost res ld ls lh o.disp o.stmt o.html).1 rfl hRc
    refine ⟨res, by rw [hv]; rfl, ld, ls, lh, ?_⟩
    rw [Kp.elim hFk]
    exact resAtL_disp hR rfl
  · rw [hab] at hRc
    unfold runWP
    jvc [runCallees, runInv, abendSig, JStrAt, argText, ite_nat_ne]
    have hpost := ‹∀ (res_1 ld ls lh : Addr) (disp st ht : List JStr), _›
    obtain ⟨hv, hR, -⟩ := (hpost res ld ls lh o.disp o.stmt o.html).2 rfl hRc
    refine ⟨res, by rw [hv]; rfl, ld, ls, lh, ?_⟩
    rw [Kp.elim hFk]
    exact resAtL_disp hR rfl

end EquivLean.Modernize.Cbstm03a.Java.Seg3

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg3 in
theorem run_cut140_vc (g : RunG) : RunCutVC g 140 inv140 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨res, ld, ls, lh, L, o, j, i, hX, hj, hm, hx, h37, h26, hi0, hile, hne⟩ := hI
  rcases Int.lt_or_le i.toInt g.crs.length with hlt | hge
  · by_cases heq : g.K3.getD i.toInt.toNat [] = sub (fixStr (g.T2.getD j []) 1000) 16 25
    · exact c140_match g args σ0 hpre fr σ res ld ls lh L o j i hX hj hm hx h37 h26 hi0 hlt hne heq
    · exact c140_miss g args σ0 hpre fr σ res ld ls lh L o j i hX hj hm hx h37 h26 hi0 hlt hne heq
  · exact c140_none g args σ0 hpre fr σ res ld ls lh L o j i hX hj hm h37 h26 hge hne

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut140_vc
