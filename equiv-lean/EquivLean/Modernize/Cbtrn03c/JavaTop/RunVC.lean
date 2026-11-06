import EquivLean.Modernize.Cbtrn03c.JavaTop.RunEntryN
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunEntryP
import EquivLean.Modernize.Cbtrn03c.JavaTop.Run34
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunExit
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunReadLo
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunReadHi
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunReadIn
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunEofLo
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunEofHi
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunEofIn
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunC52
import EquivLean.Modernize.Cbtrn03c.JavaTop.Run53ok
import EquivLean.Modernize.Cbtrn03c.JavaTop.Run53err
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunC56
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunGlue
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run` from its segments; its contract `runSpec`

At the loop head (35) the flag `eof` and the records read decide the path: the end (`eof` set),
a record read (before, after or in the date range), or the end of the file (the record area
before, after or in the date range).  After `processDetail` (53) its result decides between the
rest of the loop and the abend.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-! ## Helpers -/

/-- `l[i]? = some v` as the element at a valid index. -/
private theorem getElem_of_getElem?_eqR {l : List Value} {i : Nat} {v : Value} (h : l[i]? = some v)
    (hi : i < l.length) : l[i]'hi = v := by
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

/-- A non-negative `int` read as a natural number either way. -/
private theorem toNat_toInt_of_nonneg {i : I32} (h : 0 ≤ i.toInt) : i.toInt.toNat = i.toNat := by
  have hlt := i.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  simp only [Nat.reducePow] at h hlt ⊢
  split <;> split at h <;> omega

/-- The run's date record, when there is one, is valid. -/
private theorem dOf_valid {vals5 : Recs} (hv : ∀ v ∈ vals5, WsDateparmRecord.Valid v)
    (h5 : vals5 ≠ []) : WsDateparmRecord.Valid (dOf vals5) := by
  cases vals5 with
  | nil => exact absurd rfl h5
  | cons d rest => exact hv d List.mem_cons_self

/-! ## The verification conditions of `run` -/

theorem run_vc (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs) :
    MethodVC Gen.prog runCallees.env 1 runRef (runSpecG a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5)
      (runInv a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5) 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · -- the entry, without or with a date record
    obtain ⟨-, ⟨-, -, -, -, hf5⟩, ⟨-, -, -, -, hv5⟩, -⟩ := id hpre
    obtain h5 | ⟨d, rest, h5⟩ : vals5 = [] ∨ ∃ d rest, vals5 = d :: rest := by
      cases vals5 with
      | nil => exact Or.inl rfl
      | cons d rest => exact Or.inr ⟨d, rest, rfl⟩
    · rw [h5] at hf5
      obtain ⟨et5, ha5⟩ := parm_empty hf5
      exact run_entry_n a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 hpre h5 et5 ha5
    · rw [h5] at hf5 hv5
      have hd : WsDateparmRecord.Valid d := hv5 d List.mem_cons_self
      obtain ⟨et5, es5, e5, fs5, ha5, hl5, hle5, he5, hpe, hsd, hed⟩ := parm_elem hf5 hd
      have hdd := dOf_dates hv5
      exact run_entry_p a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 hpre d rest h5 et5 es5
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
    refine run_34 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr z h
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
        · exact run_read_lo a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv (RunAt.toR h) hini hz hlt et es e ha1 hlen h31 hil hel2 _ htf htv hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo
            (RunIs.intro (hfin.symm.trans (loop_read_lo hn hlo)))
        by_cases hhi : Model.cmpB (Model.tDate (vals1[i.toInt.toNat]'hn)) (Model.dEnd (dOf vals5)) = .gt
        · exact run_read_hi a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv (RunAt.toR h) hini hz hlt et es e ha1 hlen h31 hil hel2 _ htf htv hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo hhi
            (RunIs.intro (hfin.symm.trans (loop_read_hi hn hhi)))
        · exact run_read_in a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv (RunAt.toR h) hini hz hlt et es e ha1 hlen h31 hil hel2 _ htf htv hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo hhi h5
            ((loop_read_in hn hlo hhi).symm.trans hfin)
      · -- the end of the file
        have hge : vals1.length ≤ i.toInt := by omega
        have hgn : vals1.length ≤ i.toInt.toNat := by omega
        obtain ⟨et, es, ha1, hlen, h31⟩ := trans_arr hf1
        have hpl := procTs_len htvv
        by_cases hlo : Model.cmpB (Model.tDate tv) (Model.dStart (dOf vals5)) = .lt
        · exact run_eof_lo a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv h hini hz hge et es ha1 hlen h31 hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo
            (RunIs.intro (hfin.symm.trans (loop_eof_out hgn (Or.inl hlo))))
        by_cases hhi : Model.cmpB (Model.tDate tv) (Model.dEnd (dOf vals5)) = .gt
        · exact run_eof_hi a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv h hini hz hge et es ha1 hlen h31 hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo hhi
            (RunIs.intro (hfin.symm.trans (loop_eof_out hgn (Or.inr hhi))))
        · exact run_eof_in a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr
            i z s tv h hini hz hge et es ha1 hlen h31 hpl (tdate_len_of hpl) hdd.1 hdd.2 hlo hhi
            (RunIs.intro (hfin.symm.trans (loop_eof_in hgn hlo hhi)))
    · exact run_exit a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i z s tv
        h hz (hz1 hz)
  · -- 52: the call of `processDetail`
    obtain ⟨res, ld, lr, w, tr, i, s, t, h⟩ := hI
    have h5 : vals5 ≠ [] := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact run_c52 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i s t h hini
      (dOf_valid hv5 h5) hv2 hv3 hv4
  · -- 53: after `processDetail`: the rest of the loop, or the abend
    obtain ⟨res, ld, lr, w, tr, i, s, t, h⟩ := hI
    have hafter : afterStep vals1 vals2 vals3 vals4 (dOf vals5) i.toInt.toNat t s =
        Model.run vals1 vals2 vals3 vals4 vals5 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    cases hok : okB (Model.tranStep vals2 vals3 vals4 (dOf vals5) s t)
    · exact run_53err a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i s t h
        hok (RunIs.intro (hafter.symm.trans (afterStep_err hok)))
    · exact run_53ok a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i s t h
        hok ((afterStep_ok hok).symm.trans hafter)
  · -- 56: the call of `processEnd`
    obtain ⟨res, ld, lr, w, tr, i, s, tv, h⟩ := hI
    exact run_c56 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 fr σ res ld lr w tr i s tv h
      hini

/-! ## The contract `runSpec` -/

/-- The string a value refers to, as `JStrAt`. -/
private theorem jstrAt_of_strOf {σ : State} {v : Value} {s : JStr} (h : Jimple.strOf σ v = some s) :
    JStrAt σ v s := by
  unfold Jimple.strOf at h
  split at h
  · rename_i x
    split at h
    · rename_i s' hs
      cases h
      exact ⟨x, rfl, hs⟩
    · cases h
  · cases h

/-- The result's display list (`StrsAt`) as `runSpec` states it. -/
private theorem forall2_jstr_of_strsAt {σ : State} :
    ∀ {xs : List Value} {ss : List JStr}, StrsAt σ xs ss → Forall2 (JStrAt σ) xs ss
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [StrsAt] at h
  | _ :: _, [], h => by simp [StrsAt] at h
  | _ :: _, _ :: _, h => by
    simp only [StrsAt, List.map_cons, List.cons.injEq] at h
    exact .cons (jstrAt_of_strOf h.1) (forall2_jstr_of_strsAt h.2)

/-- A report record's text, as the record object `runSpec` states. -/
private theorem jrec_of_recText {σ : State} {v : Value} {l : List Nat}
    (h : recText σ v = some (recLine l)) :
    JRecAt FdReptfileRec "Cbtrn03c$FdReptfileRec" σ v [.str (l.map Model.ebc)] := by
  unfold recText at h
  split at h
  · rename_i x
    split at h
    · rename_i c fs hx
      split at h
      · rename_i hc
        subst hc
        split at h
        · rename_i y hy
          exact ⟨x, fs, rfl, hx, .cons ⟨y, hy, jstrAt_of_strOf h⟩ .nil⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- The result's report list (`RecsAt`) as `runSpec` states it. -/
private theorem forall2_jrec_of_recsAt {σ : State} :
    ∀ {ws : List Value} {ls : List (List Nat)}, RecsAt σ ws (ls.map recLine) →
      Forall2 (JRecAt FdReptfileRec "Cbtrn03c$FdReptfileRec" σ) ws
        (ls.map fun l => [FVal.str (l.map Model.ebc)])
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [RecsAt] at h
  | _ :: _, [], h => by simp [RecsAt] at h
  | _ :: _, _ :: _, h => by
    simp only [RecsAt, List.map_cons, List.cons.injEq] at h
    exact .cons (jrec_of_recText h.1) (forall2_jrec_of_recsAt h.2)

/-- **`run` meets `runSpec`** (given the callees' contracts). -/
theorem run_sat (hV : Valid Gen.prog runCallees.env) : Sat Gen.prog runRef runSpec := by
  intro args σ o hpre hx
  obtain ⟨vals1, vals2, vals3, vals4, vals5, hin, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9⟩ := hpre
  have key : ∀ vals1 vals2 vals3 vals4 vals5, RunIn args σ vals1 vals2 vals3 vals4 vals5 →
      ∃ a1 a2 a3 a4 a5, (runSpecG a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5).post args σ o := by
    intro vals1 vals2 vals3 vals4 vals5 hin
    obtain ⟨a1, a2, a3, a4, a5, hargs, hf1, hf2, hf3, hf4, hf5, hv1, hv2, hv3, hv4, hv5⟩ := hin
    exact ⟨a1, a2, a3, a4, a5, MethodVC.sat_of_valid hV
      (run_vc a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5) args σ o
      ⟨hargs, ⟨hf1, hf2, hf3, hf4, hf5⟩, ⟨hv1, hv2, hv3, hv4, hv5⟩,
        ⟨hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9⟩⟩ hx⟩
  cases o with
  | normal r σ' =>
    intro vals1 vals2 vals3 vals4 vals5 hin
    obtain ⟨a1, a2, a3, a4, a5, sf, ab, hrun, res, fs, l, k, xs, mods, lw, kw, ws, mw, hr, hres, hl,
      hlk, hxs, hlw, hlwk, hws, hab⟩ := key vals1 vals2 vals3 vals4 vals5 hin
    rw [RunIs.eq hrun]
    exact ⟨res, fs, l, k, xs, mods, lw, kw, ws, mw, hr, hres, hl, hlk, forall2_jstr_of_strsAt hxs, hlw,
      hlwk, forall2_jrec_of_recsAt hws, hab⟩
  | exc e σ' =>
    obtain ⟨_, _, _, _, _, hpost⟩ := key vals1 vals2 vals3 vals4 vals5 hin
    exact hpost
  | wrong m =>
    obtain ⟨_, _, _, _, _, hpost⟩ := key vals1 vals2 vals3 vals4 vals5 hin
    exact hpost

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.run_vc
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.run_sat
