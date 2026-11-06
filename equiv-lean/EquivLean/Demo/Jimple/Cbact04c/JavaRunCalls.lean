import EquivLean.Demo.Jimple.Cbact04c.JavaRunDefs

/-!
# CBACT04C in Java: `run`'s calls

The verification conditions of `run` (`Cbact04c/JavaRunDefs.lean`) from cut 21 (after `post`: the
rewrite is added to the `ArrayList`), cut 28 (`readAccount`) and cut 29 (`readRate`); the callees
are used through their contracts (`callees`).
-/

open Jimple

-- these proofs split each key comparison (`lcmp`) two ways, by `jlong_cmp_eq_zero`, not three
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Demo.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg21 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0)
    (h : J21 ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0 fr σ) :
    RunWP ca aa da acctOf rateOf cs σ0 21 fr σ := by
  obtain ⟨-, hrun⟩ := hpre
  have hrun' := Hide.intro hrun
  clear hrun
  obtain ⟨i, s, c, co, l, ys, mods, w, ⟨hloop, hi0, hilt, hcs, f15, f17, f12, f9, f6, hco, f4, hlf,
    hg, hin1, hin2, hin3⟩, hf, hne, f8, f13, f14, f16, hw, hl, hpairs⟩ := h
  have hloop' := Hide.intro hloop
  clear hloop
  obtain ⟨x, fs, t, rfl, hx, hfa, hft, ⟨ty, rfl, hty⟩, hfc, hfb⟩ := Hide.elim hco
  have hx' := heap_of_grows hg hx
  have hxl : x ≠ l := by
    intro e; subst e; exact absurd (State.lt_next_of_heap hx) (Nat.not_lt.mpr hlf)
  have hg' := Hide.intro hg
  clear hg
  unfold RunWP
  jvc [runInv, runSpecG, callees, inlineFuel, fields_get_cons, fields_get_nil, jlong_cmp_eq_zero']
  have hsel := jSel_new (acctOf := acctOf) hf hne
  have hl2 : (σ.setObj l (.list .arrayList (ys ++ [w]) (mods + 1))).heap l =
      some (.list .arrayList (ys ++ [w]) (mods + 1)) := by
    rw [State.heap_setObj, ite_eq_left rfl, ite_eq_left (State.lt_next_of_heap hl)]
  refine ⟨i, s, c, .ref x, l, ys ++ [w], mods + 1, ⟨Hide.elim hloop', hi0, hilt, hcs, ?_, ?_, ?_,
    ?_, ?_, hco, ?_, hlf, grows_setObj (Hide.elim hg') hlf, ?_, ?_, ?_⟩, Or.inr hne, ?_, ?_, ?_, ?_,
    ?_, ?_, hl2, ?_⟩
  · frame_simp [f15]
  · frame_simp [f17]
  · frame_simp [f12]
  · frame_simp [f9]
  · frame_simp [f6]
  · frame_simp [f4]
  · rw [State.initOf_setObj]; exact hin1
  · rw [State.initOf_setObj]; exact hin2
  · rw [State.initOf_setObj]; exact hin3
  · frame_simp [f8]
  · frame_simp [f13]
  · frame_simp [f14]
  · frame_simp []
  · frame_simp []
  · frame_simp []
  · rw [hsel]
    exact Hide.intro (pairs_append (acctAt_setObj_list hl (Hide.elim hw))
      (pairs_mono (fun _ _ h => acctAt_setObj_list hl h) (Hide.elim hpairs)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg28 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0)
    (h : J28 ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0 fr σ) :
    RunWP ca aa da acctOf rateOf cs σ0 28 fr σ := by
  obtain ⟨-, hrun⟩ := hpre
  have hrun' := Hide.intro hrun
  clear hrun
  obtain ⟨i, s, c, co, l, ys, mods, ⟨hloop, hi0, hilt, hcs, f15, f17, f12, f9, f6, hco, f4, hlf,
    hg, hin1, hin2, hin3⟩, hfn, f8, f13, f14, f2, f1, f0, hl, hpairs⟩ := h
  have hloop' := Hide.intro hloop
  clear hloop
  have hg' := Hide.intro hg
  clear hg
  unfold RunWP
  jvc [runInv, runSpecG, callees, inlineFuel, fields_get_cons, fields_get_nil, jlong_cmp_eq_zero']
  · obtain ⟨et, xs, h1, h2, h3, ⟨x0, hm, ha⟩, h5, h6⟩ :=
      ra_facts (Hide.elim hrun') (Hide.elim hg') (List.mem_of_getElem? hcs)
    exact ⟨et, xs, h1, h2, h3, acctOf c.acct, ⟨x0, hm, ha⟩, h5, h6⟩
  · rename_i v σ' hpost
    obtain ⟨et, xs, h1, h2, h3, ⟨x0, hm, ha⟩, h5, h6⟩ :=
      ra_facts (Hide.elim hrun') (Hide.elim hg') (List.mem_of_getElem? hcs)
    obtain ⟨v', hv, hva, rfl⟩ := hpost aa c.acct et xs (acctOf c.acct) rfl rfl h1 x0 hm ha h5 h6
    subst hv
    obtain ⟨htx, hlast, htot, hacct, hfirst⟩ := jSel_sel acctOf hfn
    refine ⟨i, s, c, co, l, ys, mods, v', ⟨Hide.elim hloop', hi0, hilt, hcs, ?_, ?_, ?_, ?_, ?_,
      hco, ?_, hlf, Hide.elim hg', hin1, hin2, hin3⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hacct, hfirst, hl,
      hpairs⟩
    · frame_simp [f15]
    · frame_simp [f17]
    · frame_simp [f12]
    · frame_simp [f9]
    · frame_simp [f6]
    · frame_simp [f4]
    · rw [htx]; frame_simp [f8]
    · frame_simp [f13]
    · frame_simp [f14]
    · rw [hlast]; frame_simp [f2]
    · rw [htot]; frame_simp [f1]
    · frame_simp [Option.getD_some]
    · rw [hacct]; exact Hide.intro hva

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg29 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0)
    (h : J29 ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0 fr σ) :
    RunWP ca aa da acctOf rateOf cs σ0 29 fr σ := by
  obtain ⟨-, hrun⟩ := hpre
  have hrun' := Hide.intro hrun
  clear hrun
  obtain ⟨i, s, c, co, l, ys, mods, r5, ⟨hloop, hi0, hilt, hcs, f15, f17, f12, f9, f6, hco, f4, hlf,
    hg, hin1, hin2, hin3⟩, f8, f13, f14, f2, f1, f16, hacc, hacceq, hfirst, hl, hpairs⟩ := h
  have hloop' := Hide.intro hloop
  clear hloop
  obtain ⟨x, fs, t, rfl, hx, hfa, hft, ⟨ty, rfl, hty⟩, hfc, hfb⟩ := Hide.elim hco
  have hx' := heap_of_grows hg hx
  have hty' := heap_of_grows hg hty
  obtain ⟨y, fy, g, rfl, hy, hyid, hybal, hycc, hycd, hyg, ⟨gy, rfl, hgy⟩⟩ := Hide.elim hacc
  have hg' := Hide.intro hg
  clear hg
  unfold RunWP
  jvc [runInv, runSpecG, callees, inlineFuel, fields_get_cons, fields_get_nil, jlong_cmp_eq_zero']
  · obtain ⟨et, xs, h1, h2, h3, ⟨x0, hm, hd⟩, h5⟩ :=
      rr_facts (Hide.elim hrun') (Hide.elim hg') (List.mem_of_getElem? hcs)
    have hgy2 : σ.heap gy = some (.str (acctOf c.acct).grp) := by rw [hgy, hacceq]
    exact ⟨(acctOf c.acct).grp, c.ty, gy, ty, c.cat, ⟨rfl, rfl, rfl⟩, hgy2, hty',
      rateOf (acctOf c.acct).grp c.ty c.cat, et, xs, h1, h2, h3, ⟨x0, hm, hd⟩, h5⟩
  · rename_i v σ' hpost
    obtain ⟨et, xs, h1, h2, h3, ⟨x0, hm, hd⟩, h5⟩ :=
      rr_facts (Hide.elim hrun') (Hide.elim hg') (List.mem_of_getElem? hcs)
    have hgy2 : σ.heap gy = some (.str (acctOf c.acct).grp) := by rw [hgy, hacceq]
    obtain ⟨hv, rfl⟩ := hpost da _ _ gy ty c.cat _ et xs rfl rfl rfl rfl hgy2 hty' h1 x0 hm hd h5
    subst hv
    refine ⟨i, s, c, .ref x, l, ys, mods, .ref y, ⟨Hide.elim hloop', hi0, hilt, hcs, ?_, ?_, ?_, ?_,
      ?_, hco, ?_, hlf, Hide.elim hg', hin1, hin2, hin3⟩, ?_, ?_, ?_, ?_, ?_, ?_, hacc, hacceq,
      hfirst, ?_, hl, hpairs⟩
    · frame_simp [f15]
    · frame_simp [f17]
    · frame_simp [f12]
    · frame_simp [f9]
    · frame_simp [f6]
    · frame_simp [f4]
    · frame_simp [f8]
    · frame_simp [f13]
    · frame_simp [f14]
    · frame_simp [f2]
    · frame_simp [f1]
    · frame_simp [f16]
    · rw [hacceq]; frame_simp [Option.getD_some]

end EquivLean.Demo.Cbact04c.Java
