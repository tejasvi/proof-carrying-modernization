import EquivLean.Modernize.Cbstm03b.Java.AcctPre

/-!
# CBSTM03B → Java, `acctProc`: keyed `READ` (operation `"K"`), up to the key loop

`keySub` gives the key text; the key loop starts with `v = 0`, `i = 0` (`J33`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem acct_key_entry {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0)
    (hop : Model.aOp a = opReadK) :
    acctWP oe st q opv oeM s a σ0 0 (Frame.init true [.ref oe, .ref st, .ref q, opv]) σ0 := by
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, hp, hpos, heof, gr, hr, gs, hq, hxop, hopv, hb, g2, g3, g4', g5, g6,
    n1, n2, n3, hI0, hF⟩ := pre_fin hpre
  subst hopv
  rw [hop] at hb
  subst hb
  rw [op_texts.2.2.1] at hxop
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  clear hpre hrec4 hl hlen hrs
  simp only [acctWP, procSpecG, Spec.of]
  jvc [acctInv, acctCallees, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, Grows, n1, n2, n3, n1', n2',
    n3']
  all_goals unfold FinCtx at hF
  all_goals obtain ⟨hS, hSep, hE, hV, hK, hdd, hI, hA, hVa, m4, hr', mr, hnr, gr', js, ha, ldd, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2', j2, j3, g4', j4, g5, g6', j6, n4, n5, n6, lst, lo4, lq, lfdr, haw0, hawr⟩ := hF
  · exact ⟨a, jRecAt_grows hA (gr_trans (gr_alloc _ _) (gr_alloc _ _)), hVa⟩
  · rename_i v σ1 hpost
    obtain ⟨x, hv, hx, hn, hh, hi, hs⟩ :=
      hpost q a rfl (jRecAt_grows hA (gr_trans (gr_alloc _ _) (gr_alloc _ _))) hVa
    subst hv
    refine ⟨hop, ⟨?_, ?_, ?_, fun fs' h => ?_⟩, x, 0, ?_, hx, ?_, ?_, Nat.zero_le _,
      ⟨Nat.le_trans (Nat.le_add_right _ 2) hn, heap_of_alloc2 hh⟩, hi, hs⟩
    all_goals simp only [Frame.get_setLocal, Frame.get_mk_empty, Option.getD_some]
    all_goals try rfl
    rw [hst] at h
    cases h
    exact g4.symm

end EquivLean.Modernize.Cbstm03b.Java.AcctP
