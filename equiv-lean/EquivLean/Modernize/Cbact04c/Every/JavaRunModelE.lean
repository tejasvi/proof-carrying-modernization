import EquivLean.Modernize.Cbact04c.Every.JavaRunModelRun

/-!
# CBACT04C → Java: the every-input model step in the phases of `run`'s loop body

On a live state (not stopped), `Model.stepE` is
* the account part `stSel` (the display line; on a new account the rewrite of the previous one and
  the lookups), when the account and its cross-reference are found, followed by the rate part:
  `stFin` at the rate of the disclosure record `discD` (the account's group, else `DEFAULT`), after
  the two lines of the `DEFAULT` retry (`selD`) — `stepE_found`;
* an abend after the rewrite, when the account or the cross-reference is missing —
  `stepE_acct_missing`, `stepE_xref_missing`;
* an abend after the retry lines, when the `DEFAULT` group is missing too — `stepE_default_missing`.
`stInv_st`: the invariant `StInv` holds of every live state.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## The rate part -/

theorem stOf_interest (parm clk : List UInt8) (s : Model.StE) (t : List FV) (r : Int) :
    stOf (s.interest parm clk t r) = stFin parm clk r (stOf s) t := by
  unfold Model.StE.interest stFin
  split <;> rfl

theorem interest_stop (parm clk : List UInt8) (s : Model.StE) (t : List FV) (r : Int) :
    (s.interest parm clk t r).stop = s.stop := by
  unfold Model.StE.interest
  split <;> rfl

theorem findRateO_eq (discs : List (List FV)) (grp ty : List UInt8) (cat : Int) :
    Model.findRateO discs grp ty cat =
      (discs.find? (fun d => Model.dGrp d == grp && Model.dType d == ty && Model.dCat d == cat)).map
        Model.dRate := rfl

/-- The rate part when a disclosure record is found (the account's group or `DEFAULT`). -/
theorem rate_found (g : G) (s : Model.StE) (t : List FV) (hd : discD g (stOf s) t ≠ []) :
    stOf (s.rate g.discs g.parm g.clk t) =
      stFin g.parm g.clk (Model.dRate (discD g (stOf s) t)) (selD g (stOf s) t) t ∧
    (s.rate g.discs g.parm g.clk t).stop = s.stop := by
  unfold Model.StE.rate
  unfold discD selD grpMissing at *
  cases hf : Model.findRateO g.discs (Model.aGrp s.acct) (Model.tType t) (Model.tCat t) with
  | some r =>
    have hf' : Model.findRateO g.discs (Model.aGrp (stOf s).acct) (Model.tType t) (Model.tCat t) =
        some r := hf
    rw [findRateO_eq, Option.map_eq_some_iff] at hf
    obtain ⟨d, hd1, hd2⟩ := hf
    have hdisc : discOf g (stOf s) t = d := by
      unfold discOf
      change (g.discs.find? (fun d => Model.dGrp d == Model.aGrp s.acct &&
        Model.dType d == Model.tType t && Model.dCat d == Model.tCat t)).getD [] = d
      rw [hd1]; rfl
    simp only [hf', Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hdisc, hd2]
    exact ⟨stOf_interest _ _ _ _ _, interest_stop _ _ _ _ _⟩
  | none =>
    have hf' : Model.findRateO g.discs (Model.aGrp (stOf s).acct) (Model.tType t) (Model.tCat t) =
        none := hf
    simp only [hf', Option.isNone_none, ↓reduceIte] at hd ⊢
    cases hf2 : Model.findRateO g.discs Model.defaultGrp (Model.tType t) (Model.tCat t) with
    | some r =>
      rw [findRateO_eq, Option.map_eq_some_iff] at hf2
      obtain ⟨d, hd1, hd2⟩ := hf2
      have hdef : defDisc g t = d := by
        unfold defDisc
        rw [hd1]; rfl
      simp only [hdef, hd2]
      exact ⟨stOf_interest _ _ _ _ _, interest_stop _ _ _ _ _⟩
    | none =>
      exfalso
      apply hd
      unfold defDisc
      rw [findRateO_eq, Option.map_eq_none_iff] at hf2
      rw [hf2]; rfl

/-- The rate part when neither the group nor `DEFAULT` has a record: the retry lines, the abend. -/
theorem rate_default_missing (g : G) (s : Model.StE) (t : List FV) (hm : grpMissing g (stOf s) t)
    (hd : defDisc g t = []) (hv : ∀ d ∈ g.discs, d ≠ []) :
    (s.rate g.discs g.parm g.clk t) =
      ({ s with disp := s.disp ++ [Model.txt "DISCLOSURE GROUP RECORD MISSING",
          Model.txt "TRY WITH DEFAULT GROUP CODE"] } : Model.StE).abend
        [Model.txt "ERROR READING DEFAULT DISCLOSURE GROUP"] := by
  unfold grpMissing at hm
  have hf : Model.findRateO g.discs (Model.aGrp s.acct) (Model.tType t) (Model.tCat t) = none :=
    Option.isNone_iff_eq_none.1 hm
  have hf2 : Model.findRateO g.discs Model.defaultGrp (Model.tType t) (Model.tCat t) = none := by
    rw [findRateO_eq, Option.map_eq_none_iff]
    unfold defDisc at hd
    cases h : g.discs.find? (fun d => Model.dGrp d == Model.defaultGrp && Model.dType d ==
        Model.tType t && Model.dCat d == Model.tCat t) with
    | none => rfl
    | some d =>
      rw [h] at hd
      exact absurd hd (hv d (List.mem_of_find?_eq_some h))
  unfold Model.StE.rate
  simp only [hf, hf2]

/-! ## The account part -/

theorem find?_getD_ne {α : Type} {l : List (List α)} {p : List α → Bool}
    (h : (l.find? p).getD [] ≠ []) : l.find? p = some ((l.find? p).getD []) := by
  cases hf : l.find? p with
  | none => rw [hf] at h; exact absurd rfl h
  | some x => rfl

theorem findAcctO_of_ne {l : List (List FV)} {id : Int} (h : Model.findAcct l id ≠ []) :
    Model.findAcctO l id = some (Model.findAcct l id) := find?_getD_ne h

theorem findXrefO_of_ne {l : List (List FV)} {id : Int} (h : Model.findXref l id ≠ []) :
    Model.findXrefO l id = some (Model.findXref l id) := find?_getD_ne h

/-- The display line of record `t`. -/
def d1E (s : Model.StE) (t : List FV) : Model.StE :=
  { s with disp := s.disp ++ [TranCatBalRecord.textS t] }

/-- The display line, then the rewrite of the previous account (if any). -/
def rwE (s : Model.StE) (t : List FV) : Model.StE :=
  if (d1E s t).lastId.isSome then
    { d1E s t with
      accts := Model.replaceFirst (fun a => Model.aId a == Model.aId (d1E s t).acct)
        (Model.posted (d1E s t).acct (d1E s t).total) (d1E s t).accts,
      rewrites := (d1E s t).rewrites ++ [Model.posted (d1E s t).acct (d1E s t).total] }
  else d1E s t

/-- The new account `a` and its cross-reference `x`, after the rewrite. -/
def selE (s : Model.StE) (t : List FV) (a x : List FV) : Model.StE :=
  { rwE s t with lastId := some (Model.tAcct t), total := 0, acct := a, xref := x }

theorem rwE_stop (s : Model.StE) (t : List FV) : (rwE s t).stop = s.stop := by
  unfold rwE; split <;> rfl

theorem selE_stop (s : Model.StE) (t : List FV) (a x : List FV) : (selE s t a x).stop = s.stop :=
  rwE_stop s t

theorem stOf_rwE (s : Model.StE) (t : List FV) : stOf (rwE s t) = stRw (stOf s) t := by
  unfold rwE stRw
  cases hl : s.lastId <;> simp [d1E, disp1, stOf, hl]

/-- The step of a new account, the lookups found. -/
theorem stepE_new (g : G) (s : Model.StE) (t : List FV) {a x : List FV} (hs : s.stop = false)
    (h : ¬ s.lastId = some (Model.tAcct t))
    (ha : Model.findAcctO (rwE s t).accts (Model.tAcct t) = some a)
    (hx : Model.findXrefO g.xrefs (Model.tAcct t) = some x) :
    g.stepE s t = (selE s t a x).rate g.discs g.parm g.clk t := by
  unfold G.stepE Model.stepE
  rw [if_neg (show ¬ (s.stop = true) by simp [hs])]
  simp only []
  rw [if_neg h]
  cases hl : s.lastId with
  | none =>
    simp only [rwE, d1E, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at ha
    simp only [selE, rwE, d1E, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ha, hx]
  | some id =>
    simp only [rwE, d1E, hl, Option.isSome_some, ↓reduceIte] at ha
    simp only [selE, rwE, d1E, hl, Option.isSome_some, ↓reduceIte, ha, hx]

/-- **A record whose lookups succeed**: the account part `stSel`, the rate part at `discD`. -/
theorem stepE_found (g : G) (s : Model.StE) (t : List FV) (hs : s.stop = false)
    (hacc : (stSel g.xrefs (stOf s) t).acct ≠ []) (hxr : (stSel g.xrefs (stOf s) t).xref ≠ [])
    (hd : discD g (stSel g.xrefs (stOf s) t) t ≠ []) :
    stOf (g.stepE s t) = stFin g.parm g.clk (Model.dRate (discD g (stSel g.xrefs (stOf s) t) t))
        (selD g (stSel g.xrefs (stOf s) t) t) t ∧ (g.stepE s t).stop = false := by
  by_cases h : s.lastId = some (Model.tAcct t)
  · -- the same account
    have hsel : stSel g.xrefs (stOf s) t = stOf (d1E s t) := by
      unfold stSel
      rw [if_pos (show (stOf s).lastId = some (Model.tAcct t) from h)]
      rfl
    rw [hsel] at hd ⊢
    have e : g.stepE s t = (d1E s t).rate g.discs g.parm g.clk t := by
      unfold G.stepE Model.stepE
      rw [if_neg (show ¬ (s.stop = true) by simp [hs])]
      simp only []
      rw [if_pos h]
      rfl
    rw [e]
    obtain ⟨h1, h2⟩ := rate_found g _ t hd
    exact ⟨h1, by rw [h2]; exact hs⟩
  · -- a new account: the rewrite of the previous one, then the lookups
    have hsel : stSel g.xrefs (stOf s) t = stOf (selE s t
        (Model.findAcct (rwE s t).accts (Model.tAcct t)) (Model.findXref g.xrefs (Model.tAcct t))) := by
      unfold stSel
      rw [if_neg (show ¬ (stOf s).lastId = some (Model.tAcct t) from h)]
      unfold stAcct selE
      rw [← stOf_rwE]
      rfl
    rw [hsel] at hd hacc hxr ⊢
    rw [stepE_new g s t hs h (findAcctO_of_ne hacc) (findXrefO_of_ne hxr)]
    obtain ⟨h1, h2⟩ := rate_found g _ t hd
    exact ⟨h1, by rw [h2, selE_stop]; exact hs⟩

/-! ## The abends -/

theorem stOf_abend (s : Model.StE) (l : List (List Nat)) :
    stOf (s.abend l) = { stOf s with disp := (stOf s).disp ++ l ++
      [Model.txt "FILE STATUS IS: NNNN0023", Model.txt "ABENDING PROGRAM"] } := rfl

theorem abend_stop (s : Model.StE) (l : List (List Nat)) : (s.abend l).stop = true := rfl

/-- A new account that is missing: the rewrite, the abend. -/
theorem stepE_acct_missing (g : G) (s : Model.StE) (t : List FV) (hs : s.stop = false)
    (h : ¬ s.lastId = some (Model.tAcct t))
    (ha : Model.findAcctO (rwE s t).accts (Model.tAcct t) = none) :
    g.stepE s t = (rwE s t).abend [Model.txt "ACCOUNT NOT FOUND: " ++
      zpad 11 (Model.tAcct t).natAbs, Model.txt "ERROR READING ACCOUNT FILE"] := by
  unfold G.stepE Model.stepE
  rw [if_neg (show ¬ (s.stop = true) by simp [hs])]
  simp only []
  rw [if_neg h]
  cases hl : s.lastId with
  | none =>
    simp only [rwE, d1E, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at ha
    simp only [rwE, d1E, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ha]
  | some id =>
    simp only [rwE, d1E, hl, Option.isSome_some, ↓reduceIte] at ha
    simp only [rwE, d1E, hl, Option.isSome_some, ↓reduceIte, ha]

/-- A new account found, its cross-reference missing: the rewrite, the abend. -/
theorem stepE_xref_missing (g : G) (s : Model.StE) (t : List FV) {a : List FV}
    (hs : s.stop = false) (h : ¬ s.lastId = some (Model.tAcct t))
    (ha : Model.findAcctO (rwE s t).accts (Model.tAcct t) = some a)
    (hx : Model.findXrefO g.xrefs (Model.tAcct t) = none) :
    g.stepE s t = (rwE s t).abend [Model.txt "ACCOUNT NOT FOUND: " ++
      zpad 11 (Model.tAcct t).natAbs, Model.txt "ERROR READING XREF FILE"] := by
  unfold G.stepE Model.stepE
  rw [if_neg (show ¬ (s.stop = true) by simp [hs])]
  simp only []
  rw [if_neg h]
  cases hl : s.lastId with
  | none =>
    simp only [rwE, d1E, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at ha
    simp only [rwE, d1E, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ha, hx]
  | some id =>
    simp only [rwE, d1E, hl, Option.isSome_some, ↓reduceIte] at ha
    simp only [rwE, d1E, hl, Option.isSome_some, ↓reduceIte, ha, hx]

/-- The state before the rate part, when the lookups succeed. -/
theorem stepE_pre (g : G) (s : Model.StE) (t : List FV) (hs : s.stop = false)
    (hacc : (stSel g.xrefs (stOf s) t).acct ≠ []) (hxr : (stSel g.xrefs (stOf s) t).xref ≠ []) :
    ∃ p : Model.StE, stOf p = stSel g.xrefs (stOf s) t ∧ p.stop = false ∧
      g.stepE s t = p.rate g.discs g.parm g.clk t := by
  by_cases h : s.lastId = some (Model.tAcct t)
  · refine ⟨d1E s t, ?_, hs, ?_⟩
    · unfold stSel
      rw [if_pos (show (stOf s).lastId = some (Model.tAcct t) from h)]
      rfl
    · unfold G.stepE Model.stepE
      rw [if_neg (show ¬ (s.stop = true) by simp [hs])]
      simp only []
      rw [if_pos h]
      rfl
  · have hsel : stSel g.xrefs (stOf s) t = stOf (selE s t
        (Model.findAcct (rwE s t).accts (Model.tAcct t)) (Model.findXref g.xrefs (Model.tAcct t))) := by
      unfold stSel
      rw [if_neg (show ¬ (stOf s).lastId = some (Model.tAcct t) from h)]
      unfold stAcct selE
      rw [← stOf_rwE]
      rfl
    rw [hsel] at hacc hxr ⊢
    exact ⟨_, rfl, by rw [selE_stop]; exact hs,
      stepE_new g s t hs h (findAcctO_of_ne hacc) (findXrefO_of_ne hxr)⟩

/-- When neither the group nor `DEFAULT` has a record: the retry lines, the abend. -/
theorem stepE_default_missing (g : G) (s : Model.StE) (t : List FV) (hs : s.stop = false)
    (hacc : (stSel g.xrefs (stOf s) t).acct ≠ []) (hxr : (stSel g.xrefs (stOf s) t).xref ≠ [])
    (hm : grpMissing g (stSel g.xrefs (stOf s) t) t) (hd : defDisc g t = [])
    (hv : ∀ d ∈ g.discs, d ≠ []) :
    stOf (g.stepE s t) = { selD g (stSel g.xrefs (stOf s) t) t with
      disp := (selD g (stSel g.xrefs (stOf s) t) t).disp ++
        [Model.txt "ERROR READING DEFAULT DISCLOSURE GROUP"] ++
        [Model.txt "FILE STATUS IS: NNNN0023", Model.txt "ABENDING PROGRAM"] } ∧
    (g.stepE s t).stop = true := by
  obtain ⟨p, hp, -, he⟩ := stepE_pre g s t hs hacc hxr
  rw [he]
  rw [← hp] at hm ⊢
  rw [rate_default_missing g p t hm hd hv]
  refine ⟨?_, rfl⟩
  unfold selD
  rw [if_pos hm]
  rfl

/-- The stop flag only goes up. -/
theorem stop_of_stepE {g : G} {s : Model.StE} {t : List FV} (h : (g.stepE s t).stop = false) :
    s.stop = false := by
  cases hs : s.stop with
  | false => rfl
  | true =>
    have : g.stepE s t = s := by simp only [G.stepE, Model.stepE, hs, ↓reduceIte]
    rw [this, hs] at h
    exact h

/-! ## The invariant along the every-input fold -/

theorem stInv_selD {g : G} {s : Model.St} (h : StInv g s) (t : List FV) : StInv g (selD g s t) := by
  unfold selD
  split
  · exact h
  · exact h

/-- The rewrite keeps the account ids. -/
theorem stRw_ids {g : G} {s : Model.St} (h : StInv g s) (t : List FV) :
    (stRw s t).accts.map Model.aId = g.accts.map Model.aId := by
  obtain ⟨hid, -, -, hcur, -⟩ := h
  unfold stRw disp1
  cases hl : s.lastId with
  | none => exact hid
  | some id =>
    obtain ⟨hacc, -, hexg, -, -⟩ := hcur id hl
    have hex' := exists_aId_of_map hid hexg
    have hspec := Model.findAcct_spec s.accts id hex'
    have hacid : Model.aId s.acct = id := by rw [hacc]; exact hspec.2
    simp only [Option.isSome_some, ↓reduceIte, hacid]
    rw [map_replaceFirst_findAcct _ _ _ _ hex' (by rw [Model.aId_posted, hacc])]
    exact hid

/-- The rate part keeps the invariant (unless it abends). -/
theorem stInv_rate {g : G} (hv : ∀ d ∈ g.discs, d ≠ []) {p : Model.StE} (h : StInv g (stOf p))
    (t : List FV) (hs : (p.rate g.discs g.parm g.clk t).stop = false) :
    StInv g (stOf (p.rate g.discs g.parm g.clk t)) := by
  by_cases hd : discD g (stOf p) t = []
  · exfalso
    unfold discD at hd
    split at hd
    · rename_i hm
      rw [rate_default_missing g p t hm hd hv] at hs
      exact absurd hs (by rw [abend_stop]; decide)
    · rename_i hm
      unfold grpMissing at hm
      cases hf : Model.findRateO g.discs (Model.aGrp (stOf p).acct) (Model.tType t) (Model.tCat t) with
      | none => rw [hf] at hm; exact hm rfl
      | some r =>
        rw [findRateO_eq, Option.map_eq_some_iff] at hf
        obtain ⟨d, hd1, -⟩ := hf
        unfold discOf at hd
        rw [hd1] at hd
        exact hv d (List.mem_of_find?_eq_some hd1) hd
  · rw [(rate_found g p t hd).1]
    exact stInv_stFin (stInv_selD h t) _ _ _ _

/-- One live step keeps the invariant (unless it abends). -/
theorem stInv_stepE {g : G} (hin : InFacts g) {s : Model.StE} (h : StInv g (stOf s))
    (hs : s.stop = false) {t : List FV} (ht : t ∈ g.tcat) (hs' : (g.stepE s t).stop = false) :
    StInv g (stOf (g.stepE s t)) := by
  by_cases hsame : s.lastId = some (Model.tAcct t)
  · have e : g.stepE s t = (d1E s t).rate g.discs g.parm g.clk t := by
      unfold G.stepE Model.stepE
      rw [if_neg (show ¬ (s.stop = true) by simp [hs])]
      simp only []
      rw [if_pos hsame]
      rfl
    rw [e] at hs' ⊢
    exact stInv_rate hin.discs_ne (p := d1E s t) (stInv_disp1 h t) t hs'
  · cases ha : Model.findAcctO (rwE s t).accts (Model.tAcct t) with
    | none =>
      rw [stepE_acct_missing g s t hs hsame ha, abend_stop] at hs'
      exact absurd hs' (by decide)
    | some a =>
      cases hx : Model.findXrefO g.xrefs (Model.tAcct t) with
      | none =>
        rw [stepE_xref_missing g s t hs hsame ha hx, abend_stop] at hs'
        exact absurd hs' (by decide)
      | some x =>
        rw [stepE_new g s t hs hsame ha hx] at hs' ⊢
        have ha' : Model.findAcct (rwE s t).accts (Model.tAcct t) = a := by
          unfold Model.findAcct
          unfold Model.findAcctO at ha
          rw [ha]; rfl
        have hx' : Model.findXref g.xrefs (Model.tAcct t) = x := by
          unfold Model.findXref
          unfold Model.findXrefO at hx
          rw [hx]; rfl
        have hsel : stOf (selE s t a x) = stSel g.xrefs (stOf s) t := by
          rw [← ha', ← hx']
          unfold stSel
          rw [if_neg (show ¬ (stOf s).lastId = some (Model.tAcct t) from hsame)]
          unfold stAcct selE
          rw [← stOf_rwE]
          rfl
        have hex : ∃ a ∈ g.accts, Model.aId a = Model.tAcct t := by
          have hmem := List.mem_of_find?_eq_some ha
          have hid := List.find?_some ha
          simp only [beq_iff_eq] at hid
          have hids := stRw_ids h t
          rw [← stOf_rwE] at hids
          exact exists_aId_of_map hids.symm ⟨a, hmem, hid⟩
        exact stInv_rate hin.discs_ne (by rw [hsel]; exact stInv_stSel h (hin.tcat_valid t ht) hex)
          t hs'

/-- **The invariant holds of every live state of the fold.** -/
theorem stInv_st {g : G} (hin : InFacts g) : ∀ n, (g.stE n).stop = false → StInv g (g.st n)
  | 0, _ => stInv_init g hin.accts_valid
  | n + 1, hs => by
    by_cases hn : n < g.tcat.length
    · have e := G.stE_succ g hn
      rw [e] at hs
      have hs0 := stop_of_stepE hs
      show StInv g (stOf (g.stE (n + 1)))
      rw [e]
      exact stInv_stepE hin (stInv_st hin n hs0) hs0 (List.getElem_mem hn) hs
    · have e : g.stE (n + 1) = g.stE n := by
        rw [G.stE_full g (by omega), G.stE_full g (by omega)]
      show StInv g (stOf (g.stE (n + 1)))
      rw [e] at hs ⊢
      exact stInv_st hin n hs

end EquivLean.Modernize.Cbact04c.Java
