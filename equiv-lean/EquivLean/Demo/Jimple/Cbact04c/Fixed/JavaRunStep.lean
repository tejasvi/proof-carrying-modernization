import EquivLean.Demo.Jimple.Cbact04c.Fixed.JavaRunDefs

/-!
# CBACT04C in Java, the fixed port: the interest step

`run_seg33` of `Cbact04c/JavaRunLoop.lean` for `Cbact04cFixed`: the verification condition of `run` from
cut 35 (after `readRate`: the interest of the record, back to the loop head).
-/

open Jimple EquivLean.Demo.Cbact04c.Java

-- these proofs split each key comparison (`lcmp`) two ways, by `jlong_cmp_eq_zero`, not three
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Demo.Cbact04c.JavaF

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg35 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0)
    (h : J35 ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0 fr σ) :
    RunWP ca aa da acctOf rateOf cs σ0 35 fr σ := by
  obtain ⟨-, hrun⟩ := hpre
  have hrun' := Hide.intro hrun
  clear hrun
  obtain ⟨i, s, c, co, l, ys, mods, r5, ⟨hloop, hi0, hilt, hcs, f4, f17, f18, f10, f19, hco, f5, hlf,
    hg, hin1, hin2, hin3⟩, f9, f14, f15, f16, f2, f1, f13, hacc, hacceq, hfirst, f3, hl, hpairs⟩ := h
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
      ?_, ?_, ?_, ?_, ?_, ?_, hl, hlf, ?_, ?_, ?_, Hide.elim hg', hin1, hin2, hin3⟩
    · rw [i32_toNat_add_one i hi0 hlt]; exact loopAt_succ (Hide.elim hloop') hcs
    · rw [i32_toInt_add_one i hi0 hlt]; omega
    · rw [i32_toInt_add_one i hi0 hlt]; omega
    · frame_simp [f4]
    · frame_simp [f17]
    · frame_simp [f18]
    · frame_simp []
    · rw [hs']; frame_simp [f9]
    · rw [hs', hfirst]; frame_simp [f14, JInt.ofBool]
    · rw [hs', hfirst]; frame_simp [f15, JInt.ofBool]
    · rw [hs', hfirst]; frame_simp [f16, JInt.ofBool]
    · rw [hs']; frame_simp [f2]
    · rw [hs']; frame_simp [f1]
    · frame_simp [f13]
    · frame_simp [f5]
    · rw [hs']; exact Hide.intro (fun _ => Hide.elim hacc)
    · rw [hs', hacceq, jSel_last]; intro _; rfl
    · rw [hs']; exact hpairs
  · -- interest posted to the total, one more transaction
    have hr : ¬ rateOf (jSel acctOf s c).acct.grp c.ty c.cat = 0 := by rw [hacceq]; exact hcond
    obtain ⟨htx, htot, hfst, hlst, hacct, hrw⟩ := jStep_rate_ne hr
    refine ⟨i + 1#32, jStep acctOf rateOf s c, r5, l, ys, mods, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, hl, hlf, ?_, ?_, ?_, Hide.elim hg', hin1, hin2, hin3⟩
    · rw [i32_toNat_add_one i hi0 hlt]; exact loopAt_succ (Hide.elim hloop') hcs
    · rw [i32_toInt_add_one i hi0 hlt]; omega
    · rw [i32_toInt_add_one i hi0 hlt]; omega
    · frame_simp [f4]
    · frame_simp [f17]
    · frame_simp [f18]
    · frame_simp []
    · rw [htx]; frame_simp []; try rfl
    · rw [hfst, hfirst]; frame_simp [f14, JInt.ofBool]
    · rw [hfst, hfirst]; frame_simp [f15, JInt.ofBool]
    · rw [hfst, hfirst]; frame_simp [f16, JInt.ofBool]
    · rw [hlst]; frame_simp [f2]
    · rw [htot, hacceq]; frame_simp []; try rfl
    · frame_simp [f13]
    · frame_simp [f5]
    · rw [hacct]; exact Hide.intro (fun _ => Hide.elim hacc)
    · rw [hacct, hlst, hacceq, jSel_last]; intro _; rfl
    · rw [hrw]; exact hpairs

end EquivLean.Demo.Cbact04c.JavaF
