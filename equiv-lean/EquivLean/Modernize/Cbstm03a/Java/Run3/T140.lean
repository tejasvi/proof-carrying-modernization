import EquivLean.Modernize.Cbstm03a.Java.Run3.Frame2
import EquivLean.Modernize.Cbstm03a.Java.RunTerm

/-!
# CBSTM03A → Java, `run`: the thin (termination) paths from cut point 140

The key search's paths decrease `runVar`: to 140 with `i#78 + 1` (`$i20 − i#78` drops by one), to 153 (the
account search's `vC4 + (n4 − 0)` lies below `vC3`, `vC3 = vC4 + vN + 1`, `n4 < vN`); `xrefSt[0]` is unchanged.
Keys exhausted: `abend`, return (no cut point).
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

theorem var_add_lt {A c c' x y : Nat} (h : c + x < c' + y) : A + c + x < A + c' + y := by omega

/-- 140 → 153: the account search starts below the key search. -/
theorem var_140_153 {args : List Value} {σ0 σ : State} {fr fr' : Frame} {i n3 n4 : I32}
    (h2 : arr0 σ fr' 2 = arr0 σ fr 2) (h26 : fr.get 26 = some (.int i)) (h27 : fr.get 27 = some (.int n3))
    (h26' : fr'.get 26 = some (.int 0)) (h28' : fr'.get 28 = some (.int n4)) (hlt : i.toInt < n3.toInt)
    (hn4 : n4.toInt < 2147483648) : runVar 153 args σ0 fr' σ < runVar 140 args σ0 fr σ := by
  simp only [runVar, locI, h2, h26, h27, h26', h28']
  apply var_add_lt
  have e3 : vC3 = vC4 + vN + 1 := rfl
  have eN : vN = 2147483648 := rfl
  have e0 : (0 : I32).toInt = 0 := by decide
  rw [e3, eN, e0]
  omega

/-- 140 → 140: one key fewer left. -/
theorem var_140_140 {args : List Value} {σ0 σ : State} {fr fr' : Frame} {i n3 : I32}
    (h2 : arr0 σ fr' 2 = arr0 σ fr 2) (h26 : fr.get 26 = some (.int i)) (h27 : fr.get 27 = some (.int n3))
    (h26' : fr'.get 26 = some (.int (i + 1))) (h27' : fr'.get 27 = some (.int n3)) (hi0 : 0 ≤ i.toInt)
    (hlt : i.toInt < n3.toInt) (hn3 : n3.toInt < 2147483648) :
    runVar 140 args σ0 fr' σ < runVar 140 args σ0 fr σ := by
  simp only [runVar, locI, h2, h26, h27, h26', h27']
  rw [toInt_add_one32 hi0 (by omega)]
  apply var_add_lt
  omega

-- 140 thin, a key left: equal (to 153) or not (to 140), both explored.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem t140_lt (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame)
    (σ : State) (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat) (i : I32)
    (hX : XCtx g σ0 fr σ res ld ls lh o L (j + 1)) (hx : XrecLocs σ fr (g.T2.getD j []))
    (h37 : fr.get 37 = some .null) (h26 : fr.get 26 = some (.int i)) (hi0 : 0 ≤ i.toInt)
    (hlt : i.toInt < g.crs.length) :
    runThinWP g args σ0 140 fr σ (runVar 140 args σ0 fr σ) := by
  have hcl := crs_len_lt hpre
  have hal := ars_len_lt hpre
  have hK3l : g.K3.length = g.crs.length := by simp [RunG.K3, RunG.T3]
  have hT3l : g.T3.length = g.crs.length := by simp [RunG.T3]
  have hik : i.toInt.toNat < g.K3.length := by omega
  have hit : i.toInt.toNat < g.T3.length := by omega
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, -, hf2, hst2, -, -, -, -, -, -, -⟩ := hX
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hinits, -⟩ := hB
  obtain ⟨-, -, hf13, hf14, -, ⟨n3, hf27, hn3⟩, ⟨n4, hf28, hn4⟩, -, -, hT3k, hT3, -, -, -, -, -, -⟩ := hT
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
  have hn3b : n3.toInt < 2147483648 := by omega
  have hn4b : n4.toInt < 2147483648 := by omega
  have hilt : i.toInt < (xs3k.length : Int) := by omega
  have hilt' : i.toInt < (xs3.length : Int) := by omega
  have hvk := Kp.intro (And.intro hcnt (And.intro hn3b (And.intro hn4b hi0)))
  clear hxs3kl hxs3l hn3 hn4 hK3l hT3l hik hit hlt hcl hal hn3b hn4b
  generalize hkk : g.K3.getD i.toInt.toNat [] = kk at hykh
  generalize hcid : sub (fixStr (g.T2.getD j []) 1000) 16 25 = cid at hx34
  clear hkk hcid
  unfold runThinWP
  jvc [runCallees, runInv, ite_nat_ne]
  all_goals
    obtain ⟨hcnt', hn3b', hn4b', hi0'⟩ := Kp.elim hvk
    first
    | ((with_reducible refine var_140_153 ?_ h26 hf27 ?_ ?_ hcnt' hn4b') <;>
        simp (config := {decide := true}) only [arr0, Frame.get_setLocal, ↓reduceIte, hf28] <;> try rfl)
    | ((with_reducible refine var_140_140 ?_ h26 hf27 ?_ ?_ hi0' hcnt' hn3b') <;>
        simp (config := {decide := true}) only [arr0, Frame.get_setLocal, ↓reduceIte, hf27] <;> try rfl)

-- 140 thin, keys exhausted: `abend`, return.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem t140_ge (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame)
    (σ : State) (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat) (i : I32)
    (hX : XCtx g σ0 fr σ res ld ls lh o L (j + 1))
    (h37 : fr.get 37 = some .null) (h26 : fr.get 26 = some (.int i))
    (hge : (g.crs.length : Int) ≤ i.toInt) :
    runThinWP g args σ0 140 fr σ (runVar 140 args σ0 fr σ) := by
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, -, -, -, -, -, -, -, -, -, -⟩ := hX
  obtain ⟨-, -, -, -, hf7, -, -, -, -, -, -, hinits, -⟩ := hB
  obtain ⟨-, -, -, -, -, ⟨n3, hf27, hn3⟩, -, -, -, -, -, -, -, -, -, -, -⟩ := hT
  have hinitC : σ.initOf "Cbstm03a" = .done := initC_of hpre hinits
  clear hinits hpre
  have hcnt : n3.toInt ≤ i.toInt := by omega
  clear hn3 hge
  unfold runThinWP
  jvc [runCallees, runInv, abendSig, ite_nat_ne]

end EquivLean.Modernize.Cbstm03a.Java.Seg3

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg3 in
theorem run_thin140 (g : RunG) : RunThinCut g 140 inv140 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨res, ld, ls, lh, L, o, j, i, hX, hj, hm, hx, h37, h26, hi0, hile, hne⟩ := hI
  rcases Int.lt_or_le i.toInt g.crs.length with hlt | hge
  · exact t140_lt g args σ0 hpre fr σ res ld ls lh L o j i hX hx h37 h26 hi0 hlt
  · exact t140_ge g args σ0 hpre fr σ res ld ls lh L o j i hX h37 h26 hge

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin140
