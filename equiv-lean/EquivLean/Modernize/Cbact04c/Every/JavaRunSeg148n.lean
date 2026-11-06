import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg148

/-!
# CBACT04C → Java, `run`: the cross-reference search (statement 148), no match at `k`
-/

open Jimple EquivLean.Cobol.Rec

-- key comparisons (`lcmp`) split two ways, by `jlong_cmp_eq_zero_iff`, not three
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg148_next (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (h : J148 g g.args σ0 fr σ)
    (hc : ∀ i k : I32, fr.get 22 = some (.int (i + 1#32)) → fr.get 23 = some (.int k) →
      k.toInt < g.xrefs.length ∧ ∀ hk : k.toInt.toNat < g.xrefs.length,
        Model.xAcct (g.xrefs[k.toInt.toNat]) ≠ Model.tAcct (g.trec i.toInt.toNat))
    (c149 : cuts.lookup 149 = none) (c150 : cuts.lookup 150 = none)
    (c151 : cuts.lookup 151 = none) (c152 : cuts.lookup 152 = none)
    (c155 : cuts.lookup 155 = none) (c156 : cuts.lookup 156 = none)
    (c148 : cuts.lookup 148 = some (J148 g g.args σ0)) :
    RunWPc g σ0 cuts 148 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, lastV, k, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, hne, f3, f12, f14,
    f25, f16, f13, f18, f23, hk0, hkle, hprev, hcore, hacct, hlast, hfrA⟩ := h
  obtain ⟨hklt, hcond⟩ := hc i k f22 f23
  have hkN : k.toInt.toNat < g.xrefs.length := by omega
  have hcond' := hcond hkN
  clear hcond
  have hvt := trec_valid hpre hn
  obtain ⟨-, hlenX, -, -⟩ := hpre.lens
  obtain ⟨xs, hx⟩ := xrefArr_of hpre (Hide.elim hcore).1
  clear hpre
  have hr := tAcct_range hvt
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  obtain ⟨⟨et, hA⟩, hf, hv⟩ := id hx
  have hxl := Forall2.length_eq hf
  have hkx : k.toInt.toNat < xs.length := by omega
  have hrel := forall2_getElem hf _ hkx
  obtain ⟨xk, fsk, hxk, hxkh, hfk⟩ := jrec_obj hrel
  have hvk := hv _ (List.getElem_mem hkN)
  have hidk := jfield_num hfk hvk (i := 2) (by decide) (fmt := {digits := 11}) (by decide)
  rw [show (CardXrefRecord.fields.getD 2 default).jname = "xrefAcctId" from rfl] at hidk
  have hidk' : Fields.get fsk ("Cbact04c$CardXrefRecord", "xrefAcctId") =
      some (.long (BitVec.ofInt 64 (Model.xAcct (g.xrefs[k.toInt.toNat])))) := hidk
  clear hidk
  have hxr := xAcct_range hvk
  have hxsk : xs[k.toInt.toNat]? = some (.ref xk) := by rw [List.getElem?_eq_getElem hkx, hxk]
  have hkt : k.toNat = k.toInt.toNat := i32_toNat_eq k hk0
  have hlenv : (BitVec.ofNat 32 g.xrefs.length).toInt = (g.xrefs.length : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  have hinit : Inits σ := (Hide.elim hcore).2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hXY : BitVec.ofInt 64 (Model.xAcct (g.xrefs[k.toInt.toNat])) ≠
      BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) :=
    fun he => hcond' (ofInt64_inj (by omega) (by omega) (by omega) (by omega) he)
  have hx' := Hide.intro hx
  have hprev' := Hide.intro hprev
  have hvt' := Hide.intro hvt
  have hr' := Hide.intro hr
  have hcond'' := Hide.intro hcond'
  clear hx hprev hvt hfk hf hv hrel hxl hr hcond'
  generalize hXE : BitVec.ofInt 64 (Model.xAcct (g.xrefs[k.toInt.toNat])) = X at hidk' hXY
  generalize hYE : BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) = Y at f13 hXY
  have hXE' := Hide.intro hXE
  have hYE' := Hide.intro hYE
  clear hXE hYE
  have hneH := Hide.intro hne
  have hfrA' := Hide.intro hfrA
  clear hne hfrA
  unfold RunWPc
  jvc [runSpecG, runC, copyXrefSig, jlong_cmp_eq_zero_iff, Grows]
  -- the next iteration (cut point 148)
  have hXE := Hide.elim hXE'
  have hYE := Hide.elim hYE'
  subst hXE hYE
  refine j148_next hn hi0 hstop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hk0 hklt hlenX htcb (Hide.elim hneH) hx'
    (Hide.elim hr').1 (Hide.elim hr').2 (Hide.elim hprev') (Hide.elim hcond'') hcore hacct hlast
    (Hide.elim hfrA')
  all_goals first
    | (locs_tac; done)
    | (frame_simp [f3, f12, f14,
        f25, f16, f13, f18, f22, f6, f4, f5]; done)
    | decide
    | skip

end EquivLean.Modernize.Cbact04c.Java
