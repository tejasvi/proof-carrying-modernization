import EquivLean.Modernize.Cbact04c.Every.JavaRunResAbend

/-!
# CBACT04C → Java, `run`: the cross-reference search (statement 148): exit, no match, match
-/

open Jimple EquivLean.Cobol.Rec

-- key comparisons (`lcmp`) split two ways, by `jlong_cmp_eq_zero_iff`, not three
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- **The search ran past the array**: the cross-reference is missing, the run abends
(statements 157, 161–171). -/
theorem run_seg148_exit (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J148 g g.args σ0 fr σ)
    (c157 : cuts.lookup 157 = none) (c161 : cuts.lookup 161 = none) (c162 : cuts.lookup 162 = none)
    (c163 : cuts.lookup 163 = none) (c164 : cuts.lookup 164 = none) (c165 : cuts.lookup 165 = none)
    (c166 : cuts.lookup 166 = none) (c167 : cuts.lookup 167 = none) (c168 : cuts.lookup 168 = none)
    (c169 : cuts.lookup 169 = none) (c170 : cuts.lookup 170 = none) (c171 : cuts.lookup 171 = none)
    (hc : ∀ i k : I32, fr.get 22 = some (.int (i + 1#32)) → fr.get 23 = some (.int k) →
      (g.xrefs.length : Int) ≤ k.toInt) :
    RunWPc g σ0 cuts 148 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, lastV, k, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, hne, f3, f12,
    f14, f25, f16, f13, f18, f23, hk0, hkle, hprev, hcore, hacct, hlast, hfresh⟩ := h
  have hklen := hc i k f22 f23
  have hvt := trec_valid hpre hn
  obtain ⟨xs, hx⟩ := xrefArr_of hpre (Hide.elim hcore).1
  clear hpre hc
  have hr := tAcct_range hvt
  obtain ⟨⟨et, hA⟩, -⟩ := id hx
  have hno := xref_none_of_exit hx hr.1 hr.2 (k := k.toInt.toNat) (by omega) (hprev et xs hA)
  have hacc : (stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct ≠ [] :=
    jrecAt_ne_nil (Hide.elim hacct) (by decide)
  obtain ⟨-, hinit, -, hres, hdisp, -⟩ := Hide.elim hcore
  obtain ⟨fsR, hR, hRd, hRw, hRr, hRa⟩ := hres
  obtain ⟨dxs, dm, hld, -⟩ := hdisp
  have hrl : hp.res ≠ hp.ld := by intro e; rw [e, hld] at hR; cases hR
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hta := toInt_ofInt64 (v := Model.tAcct (g.trec i.toInt.toNat)) (by omega) (by omega)
  have ba : -9223372036854775808 < (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat))).toInt := by
    rw [hta]; omega
  have hta' := Hide.intro hta
  have hno' := Hide.intro hno
  have hacc' := Hide.intro hacc
  have hneH := Hide.intro hne
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  clear hprev hx hno hacc hne hta hvt hacct hlast hfresh htcb
  generalize haE : BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) = a at f13 ba
  have haE' := Hide.intro haE
  clear haE
  unfold RunWPc
  jvc [runSpecG, runC, fmtUSig, Grows, evalDynamic, concatRecipe, Native.valueOfArg,
    Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, Native.primStr, JType.isRef, inlineFuel]
  have haE := Hide.elim haE'
  subst haE
  apply runPost_abend (Hide.elim hcore) hld hR
  case hout => exact out_xref_missing hn hstop (Hide.elim hneH) (Hide.elim hacc') (Hide.elim hno')
  case hld' => chain_simp
  case hR' => chain_simp
  case hag =>
    refine ⟨by simp only [State.next_setObj, State.next_alloc]; jomega, fun x hx hw => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    obtain ⟨hw1, hw2⟩ := hw
    chain_simp
  case hvs =>
    refine .cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ .nil)))
    all_goals chain_simp
    all_goals simp only [jline, List.map_append, zpad_jline, Hide.elim hta', txt_accountNotFound]
    all_goals first | rfl | decide

end EquivLean.Modernize.Cbact04c.Java
