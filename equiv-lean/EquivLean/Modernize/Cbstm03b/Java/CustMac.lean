import EquivLean.Modernize.Cbstm03b.Java.CustFin

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

theorem ne_of_heap {σ : State} {x y : Addr} {o o' : Obj} (hx : σ.heap x = some o) (hy : σ.heap y = some o')
    (h : o ≠ o') : x ≠ y := by
  intro e
  rw [e, hy] at hx
  exact h (Option.some.inj hx).symm

-- The precondition, destructured into the facts of the objects `custProc` reads.
set_option hygiene false in
macro "cust_destruct" : tactic => `(tactic| (
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩ := hpre
  have hS' := hS
  have hA' := hA
  obtain ⟨fs, hst, pT, pX, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, ⟨z1, n1, t1⟩⟩, pA⟩ := stateAtM_iff.1 hS
  clear pT pX pA
  have m1' := m1
  have j1' := j1
  obtain ⟨o1, fs1, l, et, xs, rfl, ho1, hopen, hrecs, hl, hlen, hrecsF, hposlt, hpos, heof⟩ := m1
  obtain ⟨xr, fsx, cid, cdat, sc, sd, rfl, hxr, hcr, hcidl, hcdl, gcid, jcid, gcd, jcd⟩ :=
    custRecAt_of j1 hV.2.2.2.2.2.2.1
  obtain ⟨zs, rfl, hzs⟩ := t1
  obtain ⟨q', fsq, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq, ha, hdl, hol, hrl, hkl, hkl1,
    hkl2, hfl, gdd, jdd, gop, jop, grc, jrc, gkey, jkey, gkl, gfl, jfl⟩ := areaAt_of hA hVa
  cases hqq
  obtain ⟨fsq0, hq0, hopv⟩ := hopA
  rw [hq] at hq0
  cases hq0
  rw [gop] at hopv
  cases hopv
  obtain ⟨xop, rfl, hxop⟩ := jop
  obtain ⟨b, rfl⟩ : ∃ b, op = [b] := by
    match op, hol with
    | [b], _ => exact ⟨b, rfl⟩
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hI
  have hsq : st ≠ q := ne_of_cls hst hq (by decide)
  have hso : st ≠ o1 := ne_of_cls hst ho1 (by decide)
  have hqo : q ≠ o1 := ne_of_cls hq ho1 (by decide)
  have hsx : st ≠ xr := ne_of_cls hst hxr (by decide)
  have hqx : q ≠ xr := ne_of_cls hq hxr (by decide)
  have hox : o1 ≠ xr := ne_of_cls ho1 hxr (by decide)
  have hsl : st ≠ l := ne_of_heap hst hl (by intro h; cases h)
  have hql : q ≠ l := ne_of_heap hq hl (by intro h; cases h)
  have hol' : o1 ≠ l := ne_of_heap ho1 hl (by intro h; cases h)
  have hxl' : xr ≠ l := ne_of_heap hxr hl (by intro h; cases h)
  have hlt_st := State.lt_next_of_heap hst
  have hlt_q := State.lt_next_of_heap hq
  have hlt_o1 := State.lt_next_of_heap ho1
  have hlt_xr := State.lt_next_of_heap hxr
  have hlt_l := State.lt_next_of_heap hl
  have hlt_zs := State.lt_next_of_heap hzs
  have hxsl : xs.length = s.cust.recs.length := forall2_length hrecsF
  have hop : Model.aOp a = b := by rw [ha]; rfl
  have hkept : Kept (StateAtM σ0 st s ∧ SepM σ0 st ∧
      JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a ∧ Model.LkM03bArea.Valid a ∧
      FileAtM "Cbstm03b$CustFile" "Cbstm03b$FdCustfileRec" FdCustfileRec σ0 (.ref o1) s.cust ∧
      JRecAt FdCustfileRec "Cbstm03b$FdCustfileRec" σ0 (.ref xr) s.custRec ∧
      Forall2 (fun x vals => JRecAt FdCustfileRec "Cbstm03b$FdCustfileRec" σ0 x vals) xs s.cust.recs ∧
      a = [.str dd, .str [b], .str rc, .str key, .num kl, .str fldt] ∧ s.custRec = [.str cid, .str cdat] ∧
      cid.length = 9 ∧ cdat.length = 491 ∧
      Fields.get fsx ("Cbstm03b$FdCustfileRec", "fdCustData") = some sd ∧ JStrAt σ0 sd (cp037Str cdat)) :=
    Kept.intro ⟨hS', hsep, hA', hVa, m1', j1', hrecsF, ha, hcr, hcidl, hcdl, gcd, jcd⟩
  clear hS' m1' j1' hS hrecsF hcr jcid gcd jcd hsep))

set_option hygiene false in
macro "cust_kept" : tactic => `(tactic|
  obtain ⟨hS, hsep, hA, hVa, m1, j1, hrecsF, ha, hcr, hcidl, hcdl, gcd, jcd⟩ := Kept.elim hkept)

-- The State object after a path that wrote the status only (the file object written or not).
set_option hygiene false in
macro "cS_state" : tactic => `(tactic| (
  refine finC_ex hS hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) ?_
  chsimp
  refine ⟨_, rfl, fun k h1 h2 => get_set_other h1,
    ⟨_, (get_set_other (by decide)).trans g1, fileC m1 ho1 (by keeps4_tac) (away4 hst hq ho1 hxr (by decide))
      (rec4 hst hq ho1 (nr_of_sep hsep hst g1 k1)) (by chsimp; first | rfl | exact ho1) (by cfields_close)
      (by cfields_close) (by cfields_close) (by first | decide | exact hposlt) (by cfields_close)⟩,
    ⟨_, (get_set_other (by decide)).trans k1,
      jRecAt_same j1 (by chsimp) (by keeps4_tac) (away4 hst hq ho1 hxr (by decide))⟩,
    ⟨_, get_set_same, _, rfl, ?_⟩⟩
  rw [status_text]
  chsimp
  cstatus_close))

set_option hygiene false in
macro "cS_sep" : tactic => `(tactic| (
  refine sepC hS hsep hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
    (by cfields_close) (by cfields_close) (fun x y hx hy => ?_)
  simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte] at hx hy
  rw [k1] at hx
  rw [g1] at hy
  cases hx
  cases hy
  exact notRecOf_tr ho1 (by chsimp; first | rfl | exact ho1) (by cfields_close) hrecs (by chsimp)
    (nr_of_sep hsep hst g1 k1)))

set_option hygiene false in
macro "cS_area" : tactic => `(tactic| (
  refine area_rc hA hVa hq (by keeps4_tac) (away4 (cs := []) hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
    (fun k h => get_set_other h) get_set_same ⟨_, rfl, ?_⟩
  rw [stBytes_text]
  chsimp
  cstatus_close))

-- Heap lookups through callee states too (their `Grows` facts in the context).
macro "cheap" : tactic => `(tactic| simp (disch := jdisch) only [State.heap_setObj_of_lt, State.heap_alloc, State.next_alloc, State.next_setObj, ↓reduceIte, ite_nat_ne, eq_self_iff_true, if_true, *])

set_option hygiene false in
macro "cG_state" : tactic => `(tactic| (
  refine finC_ex hS hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) ?_
  chsimp
  refine ⟨_, rfl, fun k h1 h2 => get_set_other h1,
    ⟨_, (get_set_other (by decide)).trans g1, fileC m1 ho1 (by keeps4_tac) (away4 hst hq ho1 hxr (by decide))
      (rec4 hst hq ho1 (nr_of_sep hsep hst g1 k1)) (by cheap; try rfl) (by cfields_close)
      (by cfields_close) (by cfields_close) (by first | decide | exact hposlt) (by cfields_close)⟩,
    ⟨_, (get_set_other (by decide)).trans k1,
      jRecAt_same j1 (by cheap) (by keeps4_tac) (away4 hst hq ho1 hxr (by decide))⟩,
    ⟨_, get_set_same, _, rfl, ?_⟩⟩
  rw [status_text]
  cheap))

set_option hygiene false in
macro "cG_sep" : tactic => `(tactic| (
  refine sepC hS hsep hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
    (by cfields_close) (by cfields_close) (fun x y hx hy => ?_)
  simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte] at hx hy
  rw [k1] at hx
  rw [g1] at hy
  cases hx
  cases hy
  exact notRecOf_tr ho1 (by cheap; try rfl) (by cfields_close) hrecs (by cheap) (nr_of_sep hsep hst g1 k1)))

set_option hygiene false in
macro "cG_area" : tactic => `(tactic| (
  refine area_rc hA hVa hq (by keeps4_tac) (away4 (cs := []) hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
    (fun k h => get_set_other h) get_set_same ⟨_, rfl, ?_⟩
  rw [stBytes_text]
  cheap))

-- `cheap`, with the text of a string argument read from the heap.
macro "cheapK" : tactic => `(tactic| simp (disch := jdisch) only [State.heap_setObj_of_lt, State.heap_alloc, State.next_alloc, State.next_setObj, ↓reduceIte, ite_nat_ne, eq_self_iff_true, if_true, argText, strOf, Option.getD_some, *])

-- A frame lookup in a chain of local writes.
macro "cframe" : tactic => `(tactic| first | (simp (config := {decide := true}) only [Frame.get_setLocal, Frame.get_mk_empty, ↓reduceIte]; done) | (simp (config := {decide := true}) only [Frame.get_setLocal, Frame.get_mk_empty, ↓reduceIte, Option.some.injEq, Value.int.injEq]; decide))

-- The key `fit(keySub(area), 9)` is not an updated object (it is new, or `keySub`'s result, a string).
set_option hygiene false in
macro "cust_k9" : tactic => `(tactic| (
  have hwq : w ≠ q := k9_ne hq (by assumption) (by assumption) (by assumption) (by assumption)
  have hws : w ≠ st := k9_ne hst (by assumption) (by assumption) (by assumption) (by assumption)
  have hwx : w ≠ xr := k9_ne hxr (by assumption) (by assumption) (by assumption) (by assumption)
  have hwo : w ≠ o1 := k9_ne ho1 (by assumption) (by assumption) (by assumption) (by assumption)))

-- The State object after a path that stored the key in the FD record object and wrote the status.
set_option hygiene false in
macro "cK_state" : tactic => `(tactic| (
  refine finC_ex hS hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) ?_
  chsimp
  refine ⟨_, rfl, fun k h1 h2 => get_set_other h1,
    ⟨_, (get_set_other (by decide)).trans g1, fileC_same m1 ho1 (by keeps4_tac)
      (away4 (cs := []) hst hq ho1 hxr (by decide)) (rec4 hst hq ho1 (nr_of_sep hsep hst g1 k1)) (by cheap)⟩,
    ⟨_, (get_set_other (by decide)).trans k1, ?_⟩,
    ⟨_, get_set_same, _, rfl, ?_⟩⟩
  · rw [hcr]
    simp only [List.set_cons_zero]
    try rw [ha] at hkey9
    exact custRecAt_mk (fs := Fields.set fsx ("Cbstm03b$FdCustfileRec", "fdCustId") (.ref w)) (by cheap)
      get_set_same ⟨w, rfl, by cheapK⟩ ((get_set_other (by decide)).trans gcd)
      (jstrAt_keeps (by keeps4_tac) (away4 (cs := []) hst hq ho1 hxr (by decide)) jcd)
  · rw [status_text]
    cheap
    cstatus_close))

set_option hygiene false in
macro "cK_sep" : tactic => `(tactic| (
  refine sepC hS hsep hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
    (by cfields_close) (by cfields_close) (fun x y hx hy => ?_)
  simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte] at hx hy
  rw [k1] at hx
  rw [g1] at hy
  cases hx
  cases hy
  exact notRecOf_tr ho1 (by cheap; try rfl) (by cfields_close) hrecs (by cheap) (nr_of_sep hsep hst g1 k1)))

set_option hygiene false in
macro "cK_area" : tactic => `(tactic| (
  refine area_rc hA hVa hq (by keeps4_tac) (away4 (cs := []) hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
    (fun k h => get_set_other h) get_set_same ⟨_, rfl, ?_⟩
  rw [stBytes_text]
  cheap
  cstatus_close))

end EquivLean.Modernize.Cbstm03b.Java.CustP
