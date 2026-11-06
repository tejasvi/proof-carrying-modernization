import EquivLean.Demo.Jimple.Cbact04c.JavaRunDefs

/-!
# CBACT04C in Java: `run`'s entry path, loop head and interest step

The verification conditions of `run` (`Cbact04c/JavaRunDefs.lean`) from the entry (to the loop head),
from the loop head (cut 12: loop exit with the `Result`, first record, same account, new account)
and from cut 33 (the interest of the record, back to the loop head).
-/

open Jimple

-- these proofs split each key comparison (`lcmp`) two ways, by `jlong_cmp_eq_zero`, not three
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Demo.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg0 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State)
    (hpre : runPreG ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0) :
    RunWP ca aa da acctOf rateOf cs σ0 0 (Frame.init true [.ref ca, .ref aa, .ref da]) σ0 := by
  have hpre' := Hide.intro hpre
  clear hpre
  unfold RunWP
  jvc [runInv, runSpecG, callees, inlineFuel]
  obtain ⟨-, hrun⟩ := Hide.elim hpre'
  obtain ⟨-, -, -, -, hin2, hin3, hin1⟩ := hrun
  refine ⟨0#32, jInit, .null, σ0.next, [], 0, loopAt_zero acctOf rateOf cs, by decide, by simp,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.le_refl _, Hide.intro (by simp [jInit]),
    by simp [jInit], Hide.intro (by simp [jInit, Pairs]),
    grows_setObj (grows_alloc σ0 _) (Nat.le_refl _), ?_, ?_, ?_⟩
  all_goals first
    | (frame_simp [jInit, JInt.ofBool]; done)
    | (simp [State.heap_setObj, State.next_alloc]; done)
    | (simp only [State.initOf_setObj, State.initOf_alloc]; assumption)

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg12 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0)
    (h : J12 ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0 fr σ) :
    RunWP ca aa da acctOf rateOf cs σ0 12 fr σ := by
  obtain ⟨-, hrun⟩ := hpre
  obtain ⟨⟨etc, cxs, hca, hcp⟩, hcslen, -⟩ := id hrun
  have hrun' := Hide.intro hrun
  clear hrun
  obtain ⟨i, s, r5, l, ys, mods, hloop, hi0, hilen, f15, f17, f12, f9, f8, f13, f14, f2, f1, f16,
    f4, hl, hlf, hacc, hacc2, hpairs, hg, hin1, hin2, hin3⟩ := h
  have hloop' := Hide.intro hloop
  clear hloop
  have hca' : σ.heap ca = some (.array etc cxs) := heap_of_grows hg hca
  have hcxlen : cxs.length = cs.length := pairs_length hcp
  unfold RunWP
  by_cases hc : (cs.length : Int) ≤ i.toInt
  · clear hcp
    have hg' := Hide.intro hg
    clear hg
    jvc [runInv, runSpecG, callees, inlineFuel, fields_get_cons, fields_get_nil]
    have hl' : l ≠ σ.next := State.ne_next_of_heap hl
    have hs : s = jRun acctOf rateOf cs :=
      loopAt_full (Hide.elim hloop') (by rw [i32_toNat_eq i hi0]; omega)
    subst hs
    simp only [runPostG]
    refine ⟨σ.next, ?_⟩
    simp [State.heap_setObj, State.heap_alloc, State.next_alloc, State.next_setObj, Fields.get_set,
      hl', hl]
    refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
    exact pairs_mono (fun _ _ h => acctAt_of_grows
      (grows_setObj (grows_setObj (grows_alloc _ _) (Nat.le_refl _)) (Nat.le_refl _)) h)
      (Hide.elim hpairs)
  · have hn : i.toInt.toNat < cxs.length := by omega
    have hn' : i.toInt.toNat < cs.length := by omega
    have hcat : CatAt σ0 cxs[i.toInt.toNat] cs[i.toInt.toNat] := pairs_get hcp _ hn
    have hcs : cs[i.toInt.toNat]? = some cs[i.toInt.toNat] := List.getElem?_eq_getElem hn'
    generalize cs[i.toInt.toNat] = c at hcat hcs
    have hcat' := Hide.intro hcat
    obtain ⟨x, fs, t, hxeq, hx, hfa, hft, ⟨ty, rfl, hty⟩, hfc, hfb⟩ := hcat
    have hget : cxs[i.toInt.toNat]? = some (.ref x) := by
      rw [List.getElem?_eq_getElem hn, hxeq]
    have hx' := heap_of_grows hg hx
    have hty' := heap_of_grows hg hty
    have hco : Hide (CatAt σ0 (.ref x) c) := by rw [← hxeq]; exact hcat'
    have hcs' : cs[i.toNat]? = some c := by rw [i32_toNat_eq i hi0]; exact hcs
    have hilt : i.toInt < cs.length := by omega
    clear hcp hcat'
    have hg' := Hide.intro hg
    clear hg
    cases hf : s.first
    · simp only [hf, JInt.ofBool, Bool.false_eq_true, ite_false] at f13 f14
      jvc [runInv, runSpecG, callees, inlineFuel, fields_get_cons, fields_get_nil,
        jlong_cmp_eq_zero']
      · -- the same account: J29 with `jSel = s`
        have hsel : jSel acctOf s c = s := jSel_same hf hcond
        refine ⟨i, s, c, .ref x, l, ys, mods, r5, ⟨Hide.elim hloop', hi0, hilt, hcs', ?_, ?_, ?_,
          ?_, ?_, hco, ?_, hlf, Hide.elim hg', hin1, hin2, hin3⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, hl, ?_⟩
        · frame_simp [f15]
        · frame_simp [f17]
        · frame_simp [f12]
        · frame_simp [f9]
        · frame_simp []
        · frame_simp [f4]
        · rw [hsel]; frame_simp [f8]
        · frame_simp [f13]
        · frame_simp [f14]
        · rw [hsel]; frame_simp [f2]
        · rw [hsel]; frame_simp [f1]
        · frame_simp [f16]
        · rw [hsel]; exact Hide.intro ((Hide.elim hacc) hf)
        · rw [hsel, hacc2 hf, hcond]
        · rw [hsel]; exact hf
        · rw [hsel]; exact hpairs
      · exact ⟨_, (Hide.elim hacc) hf⟩
      · -- a new account: `post` was called, J21
        rename_i v σ' hpost
        obtain ⟨w, hv, hw, hgrow, hA, hR, hC⟩ :=
          hpost r5 s.total s.acct rfl rfl ((Hide.elim hacc) hf)
        subst hv
        have hl2 : σ'.heap l = some (.list .arrayList ys mods) := by
          rw [hgrow.2 l (State.lt_next_of_heap hl), hl]
        refine ⟨i, s, c, .ref x, l, ys, mods, w, ⟨Hide.elim hloop', hi0, hilt, hcs', ?_, ?_, ?_,
          ?_, ?_, hco, ?_, hlf, grows_trans (Hide.elim hg') hgrow, hC, hA, hR⟩, hf, hcond, ?_, ?_,
          ?_, ?_, Hide.intro hw, hl2,
          Hide.intro (pairs_mono (fun _ _ h => acctAt_of_grows hgrow h) (Hide.elim hpairs))⟩
        · frame_simp [f15]
        · frame_simp [f17]
        · frame_simp [f12]
        · frame_simp [f9]
        · frame_simp []
        · frame_simp [f4]
        · frame_simp [f8]
        · frame_simp [f13]
        · frame_simp [f14]
        · frame_simp [Option.getD_some]
    · simp only [hf, JInt.ofBool, ite_true] at f13 f14
      jvc [runInv, runSpecG, callees, inlineFuel, fields_get_cons, fields_get_nil,
        jlong_cmp_eq_zero']
      -- the first record: J28
      have hsel := jSel_first (acctOf := acctOf) c hf
      refine ⟨i, s, c, .ref x, l, ys, mods, ⟨Hide.elim hloop', hi0, hilt, hcs', ?_, ?_, ?_, ?_, ?_,
        hco, ?_, hlf, Hide.elim hg', hin1, hin2, hin3⟩, Or.inl hf, ?_, ?_, ?_, ?_, ?_, ?_, hl, ?_⟩
      · frame_simp [f15]
      · frame_simp [f17]
      · frame_simp [f12]
      · frame_simp [f9]
      · frame_simp []
      · frame_simp [f4]
      · frame_simp [f8]
      · frame_simp []
      · frame_simp []
      · frame_simp []
      · frame_simp []
      · frame_simp []
      · rw [hsel]; exact hpairs

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg33 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0)
    (h : J33 ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0 fr σ) :
    RunWP ca aa da acctOf rateOf cs σ0 33 fr σ := by
  obtain ⟨-, hrun⟩ := hpre
  have hrun' := Hide.intro hrun
  clear hrun
  obtain ⟨i, s, c, co, l, ys, mods, r5, ⟨hloop, hi0, hilt, hcs, f15, f17, f12, f9, f6, hco, f4, hlf,
    hg, hin1, hin2, hin3⟩, f8, f13, f14, f2, f1, f16, hacc, hacceq, hfirst, f3, hl, hpairs⟩ := h
  have hloop' := Hide.intro hloop
  clear hloop
  obtain ⟨x, fs, t, rfl, hx, hfa, hft, ⟨ty, rfl, hty⟩, hfc, hfb⟩ := Hide.elim hco
  have hx' := heap_of_grows hg hx
  have hg' := Hide.intro hg
  clear hg
  have hcslen : cs.length < 2147483647 := (Hide.elim hrun').2.1
  have hlt : i.toInt < 2147483647 := by omega
  unfold RunWP
  jvc [runInv, runSpecG, callees, inlineFuel, fields_get_cons, fields_get_nil, jlong_cmp_eq_zero']
  · -- rate 0: no interest
    have hr : rateOf (jSel acctOf s c).acct.grp c.ty c.cat = 0 := by rw [hacceq]; exact hcond
    have hs' := jStep_rate_zero hr
    refine ⟨i + 1#32, jStep acctOf rateOf s c, r5, l, ys, mods, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, hl, hlf, ?_, ?_, ?_, Hide.elim hg', hin1, hin2, hin3⟩
    · rw [i32_toNat_add_one i hi0 hlt]; exact loopAt_succ (Hide.elim hloop') hcs
    · rw [i32_toInt_add_one i hi0 hlt]; omega
    · rw [i32_toInt_add_one i hi0 hlt]; omega
    · frame_simp [f15]
    · frame_simp [f17]
    · frame_simp [f12]
    · frame_simp []
    · rw [hs']; frame_simp [f8]
    · rw [hs', hfirst]; frame_simp [f13, JInt.ofBool]
    · rw [hs', hfirst]; frame_simp [f14, JInt.ofBool]
    · rw [hs']; frame_simp [f2]
    · rw [hs']; frame_simp [f1]
    · frame_simp [f16]
    · frame_simp [f4]
    · rw [hs']; exact Hide.intro (fun _ => Hide.elim hacc)
    · rw [hs', hacceq, jSel_last]; intro _; rfl
    · rw [hs']; exact hpairs
  · -- interest posted to the total, one more transaction
    have hr : ¬ rateOf (jSel acctOf s c).acct.grp c.ty c.cat = 0 := by rw [hacceq]; exact hcond
    obtain ⟨htx, htot, hfst, hlst, hacct, hrw⟩ := jStep_rate_ne hr
    refine ⟨i + 1#32, jStep acctOf rateOf s c, r5, l, ys, mods, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, hl, hlf, ?_, ?_, ?_, Hide.elim hg', hin1, hin2, hin3⟩
    · rw [i32_toNat_add_one i hi0 hlt]; exact loopAt_succ (Hide.elim hloop') hcs
    · rw [i32_toInt_add_one i hi0 hlt]; omega
    · rw [i32_toInt_add_one i hi0 hlt]; omega
    · frame_simp [f15]
    · frame_simp [f17]
    · frame_simp [f12]
    · frame_simp []
    · rw [htx]; frame_simp []; try rfl
    · rw [hfst, hfirst]; frame_simp [f13, JInt.ofBool]
    · rw [hfst, hfirst]; frame_simp [f14, JInt.ofBool]
    · rw [hlst]; frame_simp [f2]
    · rw [htot, hacceq]; frame_simp []; try rfl
    · frame_simp [f16]
    · frame_simp [f4]
    · rw [hacct]; exact Hide.intro (fun _ => Hide.elim hacc)
    · rw [hacct, hlst, hacceq, jSel_last]; intro _; rfl
    · rw [hrw]; exact hpairs

end EquivLean.Demo.Cbact04c.Java
