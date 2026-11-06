-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/JavaTermTop.lean (sha256 47165713c38854b9...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunVC
import EquivLean.Modernize.Cbtrn03c.JavaTop.PdVC
import EquivLean.Modernize.Cbtrn03c.JavaTop.PeVC
import EquivLean.Modernize.Cbtrn03c.TermPd15
import EquivLean.Modernize.Cbtrn03c.TermPd19n
import EquivLean.Modernize.Cbtrn03c.TermPd19p
import EquivLean.Modernize.Cbtrn03c.TermPd35n
import EquivLean.Modernize.Cbtrn03c.TermPd35p
import EquivLean.Modernize.Cbtrn03c.TermPd49n
import EquivLean.Modernize.Cbtrn03c.TermPd49p
import EquivLean.Modernize.Cbtrn03c.TermPdCalls
import EquivLean.Modernize.Cbtrn03c.TermPdEntry
import EquivLean.Modernize.Cbtrn03c.TermPeCall1
import EquivLean.Modernize.Cbtrn03c.TermPeCall2
import EquivLean.Modernize.Cbtrn03c.TermPeEntry
import EquivLean.Modernize.Cbtrn03c.TermRun34
import EquivLean.Modernize.Cbtrn03c.TermRun53err
import EquivLean.Modernize.Cbtrn03c.TermRun53ok
import EquivLean.Modernize.Cbtrn03c.TermRunC52
import EquivLean.Modernize.Cbtrn03c.TermRunC56
import EquivLean.Modernize.Cbtrn03c.TermRunEntryN
import EquivLean.Modernize.Cbtrn03c.TermRunEntryP
import EquivLean.Modernize.Cbtrn03c.TermRunEofHi
import EquivLean.Modernize.Cbtrn03c.TermRunEofIn
import EquivLean.Modernize.Cbtrn03c.TermRunEofLo
import EquivLean.Modernize.Cbtrn03c.TermRunExit
import EquivLean.Modernize.Cbtrn03c.TermRunReadHi
import EquivLean.Modernize.Cbtrn03c.TermRunReadIn
import EquivLean.Modernize.Cbtrn03c.TermRunReadLo

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, termination: the top layer (`run`, `processDetail`, `processEnd`)

The thin VCs of `run_vc`, `pd_vc`, `pe_vc`, assembled from the thin twins of their segments as
the originals are (the case analyses copied, the segment theorems replaced by their twins); with
the `MethodVC`s, termination given the callees' contracts and their termination
(`run_term_of_leaves`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

-- (copied from `RunVC`, where they are private)
private theorem getElem_of_getElem?_eqR {l : List Value} {i : Nat} {v : Value} (h : l[i]? = some v)
    (hi : i < l.length) : l[i]'hi = v := by
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

private theorem dOf_valid {vals5 : Recs} (hv : ∀ v ∈ vals5, WsDateparmRecord.Valid v)
    (h5 : vals5 ≠ []) : WsDateparmRecord.Valid (dOf vals5) := by
  cases vals5 with
  | nil => exact absurd rfl h5
  | cons d rest => exact hv d List.mem_cons_self


theorem pd_thin (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs) :
    ThinVC Gen.prog pdCallees.env 0 pdRef (pdSpecG w ld lr c a2 a3 a4 d t s xs ys cs) (pdInv w ld lr c a2 a3 a4 d t s xs ys cs) lineVs 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · exact pd_entry_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 hpre (TranFieldsI.intro hpre.2.2.1)
  intro p hp fr σ hI
  obtain ⟨-, -, -, htv, hdv, -, -, -, hxv, hyv, hcv, -, -⟩ := hpre
  simp only [pdInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hC, hW, hcard, hfirst⟩ := hI
    exact pd_c14_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcard hfirst
  · obtain ⟨hC, hW, hcard⟩ := hI
    exact pd_15_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcard
  · obtain ⟨hC, hW, hcard, y, hy, hys⟩ := hI
    exact pd_c18_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcard y hy hys hxv
  · obtain ⟨hC, hW, hcard, hi8⟩ := hI
    rcases findIdx_cases (fun x => Model.xCard x == Model.tCard t) xs with hneg | ⟨i, hpos⟩
    · exact pd_19n_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hi8 hneg
        (tranStep_xref_none hcard hneg)
    · obtain ⟨hil, -⟩ := findIdx_nat hpos
      obtain ⟨hco, hcs⟩ := cardStep_xref hcard hpos hil
      have hxf := hC.2.2.2.2.2.2.1
      obtain ⟨et, es, e, fs, ha2, hlen, hiles, hel, he, hacct⟩ := xref_elem hxf hxv hil
      have hix : i < 2147483648 := by have := xref_len hxf; omega
      exact pd_19p_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW i hpos
        (by have := xref_len hxf; omega) hi8 et es e fs ha2 hiles (getElem_of_getElem?_eq hel hiles)
        (ofInt32_toNat_small hix) he (xs[i]'hil) hacct (xacct_bound (hxv _ (List.getElem_mem hil)))
        hco hcs
  · obtain ⟨hC, hW, hcs, y, hy, hys⟩ := hI
    exact pd_c34_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcs y hy hys hyv
  · obtain ⟨hC, hW, hcs, hi8⟩ := hI
    rcases findIdx_cases (fun y => Model.yType y == Model.tType t) ys with hneg | ⟨i, hpos⟩
    · exact pd_35n_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hi8 hneg
        (tranStep_type_none (cs := cs) (d := d) hcs hneg)
    · obtain ⟨hil, -⟩ := findIdx_nat hpos
      have hyf := hC.2.2.2.2.2.2.2.1
      exact pd_35p_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcs i hpos
        (by have := type_len hyf; omega) hi8
  · obtain ⟨hC, hW, hcs, hti, hi8, hl1, y, hy, hys⟩ := hI
    exact pd_c48_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcs hti hi8 hl1 y hy hys hcv
      (tcat_bound htv)
  · obtain ⟨hC, hW, hcs, hti, hi8, hi9⟩ := hI
    obtain ⟨i, hi⟩ : ∃ i : Nat, typeIdx ys (Model.tType t) = (i : Int) :=
      ⟨(typeIdx ys (Model.tType t)).toNat, by omega⟩
    rcases findIdx_cases (fun c => Model.cType c == Model.tType t && Model.cCat c == Model.tCat t)
        cs with hneg | ⟨j, hpos⟩
    · exact pd_49n_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hi9 hneg (tcat_bound htv)
        (tranStep_cat_none (d := d) hcs hi hneg)
    · obtain ⟨htr, hil, hjl, hty, hca⟩ := tranStep_report (d := d) hcs hi hpos
      have hyf := hC.2.2.2.2.2.2.2.1
      have hcf := hC.2.2.2.2.2.2.2.2.1
      obtain ⟨et3, es3, e3, fs3, ha3, hlen3, hiles3, hel3, he3, hd3⟩ := type_elem hyf hyv hil
      obtain ⟨et4, es4, e4, fs4, ha4, hlen4, hjles4, hel4, he4, hd4⟩ := cat_elem hcf hcv hjl
      rw [hi] at hi8
      have hi9' : fr.get 9 = some (.int (BitVec.ofInt 32 (j : Int))) := by
        simpa only [catIdx, hpos] using hi9
      have hi32 : i < 2147483648 := by have := type_len hyf; omega
      have hj32 : j < 2147483648 := by have := cat_len hcf; omega
      exact pd_49p_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW htr
        (hty ▸ hyv _ (List.getElem_mem hil)) (hca ▸ hcv _ (List.getElem_mem hjl)) i j
        (by have := type_len hyf; omega) (by have := cat_len hcf; omega) hi8 hi9'
        et3 es3 e3 fs3 ha3 hiles3 (getElem_of_getElem?_eq hel3 hiles3) (ofInt32_toNat_small hi32) he3
        (hty ▸ hd3) et4 es4 e4 fs4 ha4 hjles4 (getElem_of_getElem?_eq hel4 hjles4)
        (ofInt32_toNat_small hj32) he4 (hca ▸ hd4)
  · obtain ⟨hC, hW, htr, htyv, hcav, ty, ca, hty, hca, htys, hcas⟩ := hI
    exact pd_c66_t w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW htr htyv hcav ty ca hty hca htys
      hcas htv hdv


theorem pe_thin (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St) :
    ThinVC Gen.prog peCallees.env 0 peRef (peSpecG w ld lr c d t s) (peInv w ld lr d t s) lineVs 100 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨pe_entry_t w ld lr c d t s args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [peInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl
  · exact pe_call1_t w ld lr c d t s args σ0 fr σ hI
  · exact pe_call2_t w ld lr c d t s args σ0 fr σ hI


theorem run_thin (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs) :
    ThinVC Gen.prog runCallees.env 1 runRef (runSpecG a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5) (runInv a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5) runVs 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · -- the entry, without or with a date record
    obtain ⟨-, ⟨-, -, -, -, hf5⟩, ⟨-, -, -, -, hv5⟩, -⟩ := id hpre
    obtain h5 | ⟨d, rest, h5⟩ : vals5 = [] ∨ ∃ d rest, vals5 = d :: rest := by
      cases vals5 with
      | nil => exact Or.inl rfl
      | cons d rest => exact Or.inr ⟨d, rest, rfl⟩
    · rw [h5] at hf5
      obtain ⟨et5, ha5⟩ := parm_empty hf5
      exact run_tentry_n a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 hpre h5 et5 ha5
    · rw [h5] at hf5 hv5
      have hd : WsDateparmRecord.Valid d := hv5 d List.mem_cons_self
      obtain ⟨et5, es5, e5, fs5, ha5, hl5, hle5, he5, hpe, hsd, hed⟩ := parm_elem hf5 hd
      have hdd := dOf_dates hv5
      exact run_tentry_p a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 hpre d rest h5 et5 es5
        e5 fs5 ha5 hl5 hle5 (getElem_of_getElem?_eqR he5 hl5) hpe hsd hed hdd.1 hdd.2
  intro p hp fr σ hI
  have hini : RunInits σ0 := hpre.2.2.2
  obtain ⟨-, -, ⟨hv1, hv2, hv3, hv4, hv5⟩, -⟩ := hpre
  simp only [runInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · -- 34: `eof` set exactly when there is no date record
    obtain ⟨res, ld, lr, w, tr, z, h⟩ := hI
    have hz := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    refine run_t34 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr z h
      tran0_valid ?_ ?_
    · intro hz0
      cases vals5 with
      | nil =>
        simp at hz
        rw [hz] at hz0
        exact absurd hz0 (by decide)
      | cons d rest => exact ⟨List.cons_ne_nil d rest, (run_parm vals1 vals2 vals3 vals4 d rest).symm⟩
    · intro hz1
      by_cases h5 : vals5 = []
      · subst h5
        exact RunIs.intro (run_noparm vals1 vals2 vals3 vals4)
      · simp only [h5, ↓reduceIte] at hz
        exact absurd hz hz1
  · -- 35: the loop head
    obtain ⟨res, ld, lr, w, tr, i, z, s, tv, h⟩ := hI
    have hc := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, htvv, ⟨hf1, -, -, -, -⟩, -, -, -, hi0, -, hz0,
      hz1⟩ := hc
    by_cases hz : z = 0
    · obtain ⟨h5, hfin⟩ := hz0 hz
      have hdd := dOf_dates hv5
      by_cases hlt : i.toInt < vals1.length
      · -- a record read
        have hn : i.toInt.toNat < vals1.length := by omega
        obtain ⟨et, es, e, ha1, hlen, hel, htf⟩ := trans_elem hf1 hv1 hn
        obtain ⟨-, -, -, -, h31⟩ := trans_arr hf1
        have htv := hv1 _ (List.getElem_mem hn)
        have hpl := procTs_len htv
        have hil : i.toInt.toNat < es.length := by rw [hlen]; exact hn
        have hel2 := getElem_of_getElem?_eqR hel hil
        by_cases hlo : Model.cmpB (Model.tDate (vals1[i.toInt.toNat]'hn)) (Model.dStart (dOf vals5)) = .lt
        · exact run_tread_lo a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv (RunAt.toR h) hini hz hlt et es e ha1 hlen h31 hil hel2 _ htf htv hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo
            (RunIs.intro (hfin.symm.trans (loop_read_lo hn hlo)))
        by_cases hhi : Model.cmpB (Model.tDate (vals1[i.toInt.toNat]'hn)) (Model.dEnd (dOf vals5)) = .gt
        · exact run_tread_hi a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv (RunAt.toR h) hini hz hlt et es e ha1 hlen h31 hil hel2 _ htf htv hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo hhi
            (RunIs.intro (hfin.symm.trans (loop_read_hi hn hhi)))
        · exact run_tread_in a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv (RunAt.toR h) hini hz hlt et es e ha1 hlen h31 hil hel2 _ htf htv hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo hhi h5
            ((loop_read_in hn hlo hhi).symm.trans hfin)
      · -- the end of the file
        have hge : vals1.length ≤ i.toInt := by omega
        have hgn : vals1.length ≤ i.toInt.toNat := by omega
        obtain ⟨et, es, ha1, hlen, h31⟩ := trans_arr hf1
        have hpl := procTs_len htvv
        by_cases hlo : Model.cmpB (Model.tDate tv) (Model.dStart (dOf vals5)) = .lt
        · exact run_teof_lo a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv h hini hz hge et es ha1 hlen h31 hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo
            (RunIs.intro (hfin.symm.trans (loop_eof_out hgn (Or.inl hlo))))
        by_cases hhi : Model.cmpB (Model.tDate tv) (Model.dEnd (dOf vals5)) = .gt
        · exact run_teof_hi a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv h hini hz hge et es ha1 hlen h31 hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo hhi
            (RunIs.intro (hfin.symm.trans (loop_eof_out hgn (Or.inr hhi))))
        · exact run_teof_in a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv h hini hz hge et es ha1 hlen h31 hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo hhi
            (RunIs.intro (hfin.symm.trans (loop_eof_in hgn hlo hhi)))
    · exact run_texit a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i z s tv
        h hz (hz1 hz)
  · -- 52: the call of `processDetail`
    obtain ⟨res, ld, lr, w, tr, i, s, t, h⟩ := hI
    have h5 : vals5 ≠ [] := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact run_tc52 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i s t h hini
      (dOf_valid hv5 h5) hv2 hv3 hv4
  · -- 53: after `processDetail`: the rest of the loop, or the abend
    obtain ⟨res, ld, lr, w, tr, i, s, t, h⟩ := hI
    have hafter : afterStep vals1 vals2 vals3 vals4 (dOf vals5) i.toInt.toNat t s =
        Model.run vals1 vals2 vals3 vals4 vals5 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    cases hok : okB (Model.tranStep vals2 vals3 vals4 (dOf vals5) s t)
    · exact run_t53err a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i s t h
        hok (RunIs.intro (hafter.symm.trans (afterStep_err hok)))
    · exact run_t53ok a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i s t h
        hok ((afterStep_ok hok).symm.trans hafter)
  · -- 56: the call of `processEnd`
    obtain ⟨res, ld, lr, w, tr, i, s, tv, h⟩ := hI
    exact run_tc56 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i s tv h
      hini

/-! ## Termination, given the callees' contracts and their termination -/

theorem pd_termG (hV : Valid Gen.prog pdCallees.env) (hT : ∀ p ∈ pdCallees, ContractTerm Gen.prog p.1 p.2)
    (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs) :
    ∀ args σ, (pdSpecG w ld lr c a2 a3 a4 d t s xs ys cs).pre args σ → MTerm Gen.prog pdRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) hV (Contracts.term_of_ok hT _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (pd_vc w ld lr c a2 a3 a4 d t s xs ys cs)
      (pd_thin w ld lr c a2 a3 a4 d t s xs ys cs))

theorem pd_term (hV : Valid Gen.prog pdCallees.env) (hT : ∀ p ∈ pdCallees, ContractTerm Gen.prog p.1 p.2) :
    ∀ args σ, processDetailSpecM.pre args σ → MTerm Gen.prog pdRef args σ := by
  intro args σ hpre
  obtain ⟨w, ld, lr, c, a2, a3, a4, d, s, t, xs, ys, cs, hargs, hws, htf, htv, hdv, hxf, hyf, hcf,
    hxv, hyv, hcv, hi1, hi2⟩ := hpre
  exact pd_termG hV hT w ld lr c a2 a3 a4 d t s xs ys cs args σ
    ⟨hargs, hws, htf, htv, hdv, hxf, hyf, hcf, hxv, hyv, hcv, hi1, hi2⟩

set_option maxHeartbeats 0 in
theorem pd_cterm (hV : Valid Gen.prog pdCallees.env) (hT : ∀ p ∈ pdCallees, ContractTerm Gen.prog p.1 p.2) :
    ContractTerm Gen.prog processDetailSig processDetailSpecM := by
  jcontract_term [pd_term hV hT]

theorem pe_termG (hV : Valid Gen.prog peCallees.env) (hT : ∀ p ∈ peCallees, ContractTerm Gen.prog p.1 p.2)
    (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St) :
    ∀ args σ, (peSpecG w ld lr c d t s).pre args σ → MTerm Gen.prog peRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) hV (Contracts.term_of_ok hT _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (pe_vc w ld lr c d t s) (pe_thin w ld lr c d t s))

theorem pe_term (hV : Valid Gen.prog peCallees.env) (hT : ∀ p ∈ peCallees, ContractTerm Gen.prog p.1 p.2) :
    ∀ args σ, processEndSpecM.pre args σ → MTerm Gen.prog peRef args σ := by
  intro args σ hpre
  obtain ⟨w, ld, lr, c, d, s, t, hargs, hws, htf, hvt, hi1, hi2⟩ := hpre
  exact pe_termG hV hT w ld lr c d t s args σ ⟨hargs, hws, htf, tamt_bound hvt, hi1, hi2⟩

set_option maxHeartbeats 0 in
theorem pe_cterm (hV : Valid Gen.prog peCallees.env) (hT : ∀ p ∈ peCallees, ContractTerm Gen.prog p.1 p.2) :
    ContractTerm Gen.prog processEndSig processEndSpecM := by
  jcontract_term [pe_term hV hT]

theorem run_termG (hV : Valid Gen.prog runCallees.env)
    (hT : ∀ p ∈ runCallees, ContractTerm Gen.prog p.1 p.2) (a1 a2 a3 a4 a5 : Addr)
    (vals1 vals2 vals3 vals4 vals5 : Recs) :
    ∀ args σ, (runSpecG a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5).pre args σ →
      MTerm Gen.prog runRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) hV (Contracts.term_of_ok hT _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (run_vc a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5)
      (run_thin a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5))

theorem run_term_of (hV : Valid Gen.prog runCallees.env)
    (hT : ∀ p ∈ runCallees, ContractTerm Gen.prog p.1 p.2) :
    ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ := by
  intro args σ hpre
  obtain ⟨vals1, vals2, vals3, vals4, vals5, hin, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9⟩ := hpre
  obtain ⟨a1, a2, a3, a4, a5, hargs, hf1, hf2, hf3, hf4, hf5, hv1, hv2, hv3, hv4, hv5⟩ := hin
  exact run_termG hV hT a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ
    ⟨hargs, ⟨hf1, hf2, hf3, hf4, hf5⟩, ⟨hv1, hv2, hv3, hv4, hv5⟩, ⟨hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9⟩⟩

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.run_term_of
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_cterm
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pe_cterm
