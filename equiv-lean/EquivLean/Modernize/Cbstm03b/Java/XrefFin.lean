import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03B → Java: the end of an XREFFILE procedure's path

The XREFFILE versions of the file-specific parts of `TrnxFin.lean` (the generic lemmas and closers there are
reused): the State object's other fields are kept, its XREFFILE parts hold the new values; the objects a path may
update are the State object, the area and the XREFFILE file object (`ChgX`), or only the first two (`ChgS`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-- The classes of the parts of the state other than XREFFILE's. -/
abbrev otherX : List ClassName := ["Cbstm03b$TrnxFile", "Cbstm03b$FdTrnxfileRec", "Cbstm03b$CustFile",
  "Cbstm03b$FdCustfileRec", "Cbstm03b$AcctFile", "Cbstm03b$FdAcctfileRec"]

/-- **The state after an XREFFILE path**: the State object's other fields are kept, its XREFFILE parts hold the
new values. -/
theorem finX {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs fs' : List (FieldKey × Value)} {A : Addr → Prop}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps A σ0 σ') (ha : Away A σ0 otherX)
    (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hkeep : ∀ k, k ≠ ("Cbstm03b$State", "xreffileStatus") → k ≠ ("Cbstm03b$State", "fdXreffileRec") →
      Fields.get fs' k = Fields.get fs k)
    (hpart : PartX σ' fs' f' r' c') :
    StateAtM σ' st { s with xref := f', xrefRec := r', xrefSt := c' } ∧ SepM σ' st := by
  obtain ⟨fs0, hst0, pT, -, pC, pA⟩ := stateAtM_iff.1 hs
  rw [hst] at hst0
  cases hst0
  refine ⟨stateAtM_iff.2 ⟨fs', hst', ?_, hpart, ?_, ?_⟩, ?_⟩
  · exact (pT.fields (hkeep _ (by decide) (by decide)) (hkeep _ (by decide) (by decide))
      (hkeep _ (by decide) (by decide))).keeps hk (ha.mono (by decide))
  · exact (pC.fields (hkeep _ (by decide) (by decide)) (hkeep _ (by decide) (by decide))
      (hkeep _ (by decide) (by decide))).keeps hk (ha.mono (by decide))
  · exact (pA.fields (hkeep _ (by decide) (by decide)) (hkeep _ (by decide) (by decide))
      (hkeep _ (by decide) (by decide))).keeps hk (ha.mono (by decide))
  · exact sepM_keeps hs hsep hk (ha.mono (by decide)) hst'
      (fun fs0 h0 => by
        rw [hst] at h0
        cases h0
        exact ⟨hkeep _ (by decide) (by decide), hkeep _ (by decide) (by decide), hkeep _ (by decide) (by decide),
          hkeep _ (by decide) (by decide)⟩)

theorem finX_state {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs fs' : List (FieldKey × Value)} {A : Addr → Prop}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps A σ0 σ') (ha : Away A σ0 otherX)
    (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hkeep : ∀ k, k ≠ ("Cbstm03b$State", "xreffileStatus") → k ≠ ("Cbstm03b$State", "fdXreffileRec") →
      Fields.get fs' k = Fields.get fs k)
    (hpart : PartX σ' fs' f' r' c') :
    StateAtM σ' st { s with xref := f', xrefRec := r', xrefSt := c' } :=
  (finX hs hsep hst hk ha hst' hkeep hpart).1

theorem finX_sep {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs fs' : List (FieldKey × Value)} {A : Addr → Prop}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps A σ0 σ') (ha : Away A σ0 otherX)
    (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hkeep : ∀ k, k ≠ ("Cbstm03b$State", "xreffileStatus") → k ≠ ("Cbstm03b$State", "fdXreffileRec") →
      Fields.get fs' k = Fields.get fs k) :
    SepM σ' st :=
  sepM_keeps hs hsep hk (ha.mono (by decide)) hst'
    (fun fs0 h0 => by
      rw [hst] at h0
      cases h0
      exact ⟨hkeep _ (by decide) (by decide), hkeep _ (by decide) (by decide), hkeep _ (by decide) (by decide),
        hkeep _ (by decide) (by decide)⟩)

/-- The objects an XREFFILE path may update: the State object, the area, the file (by class). -/
def ChgX (σ0 : State) (x : Addr) : Prop :=
  ∃ c fs, σ0.heap x = some (.plain c fs) ∧ c ∈ ["Cbstm03b$State", "Cbstm03b$LkM03bArea", "Cbstm03b$XrefFile"]

theorem away_chgX (σ0 : State) : Away (ChgX σ0) σ0 (otherX ++ ["Cbstm03b$FdXreffileRec"]) := by
  rintro y ⟨c, fs, h, hc⟩
  have hd : ∀ c ∈ ["Cbstm03b$State", "Cbstm03b$LkM03bArea", "Cbstm03b$XrefFile"],
      c ∉ otherX ++ ["Cbstm03b$FdXreffileRec"] := by decide
  exact ⟨c, fs, h, hd c hc⟩

theorem chgX_of {σ0 : State} {x : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    (h : σ0.heap x = some (.plain c fs))
    (hc : c ∈ ["Cbstm03b$State", "Cbstm03b$LkM03bArea", "Cbstm03b$XrefFile"] := by decide) : ChgX σ0 x :=
  ⟨c, fs, h, hc⟩

/-- `finX_state` and `finX_sep` with the new State field list as a witness. -/
theorem finX_ex {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs : List (FieldKey × Value)}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps (ChgX σ0) σ0 σ')
    (h : ∃ fs', σ'.heap st = some (.plain "Cbstm03b$State" fs') ∧
      (∀ k, k ≠ ("Cbstm03b$State", "xreffileStatus") → k ≠ ("Cbstm03b$State", "fdXreffileRec") →
        Fields.get fs' k = Fields.get fs k) ∧ PartX σ' fs' f' r' c') :
    StateAtM σ' st { s with xref := f', xrefRec := r', xrefSt := c' } ∧ SepM σ' st := by
  obtain ⟨fs', h1, h2, h3⟩ := h
  exact finX hs hsep hst hk ((away_chgX σ0).mono (by decide)) h1 h2 h3

/-- The same for a path that keeps the file object. -/
theorem finXS_ex {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs : List (FieldKey × Value)}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps (ChgS σ0) σ0 σ')
    (h : ∃ fs', σ'.heap st = some (.plain "Cbstm03b$State" fs') ∧
      (∀ k, k ≠ ("Cbstm03b$State", "xreffileStatus") → k ≠ ("Cbstm03b$State", "fdXreffileRec") →
        Fields.get fs' k = Fields.get fs k) ∧ PartX σ' fs' f' r' c') :
    StateAtM σ' st { s with xref := f', xrefRec := r', xrefSt := c' } ∧ SepM σ' st := by
  obtain ⟨fs', h1, h2, h3⟩ := h
  exact finX hs hsep hst hk ((away_chgS σ0).mono (by decide)) h1 h2 h3

macro "keepsX_tac" : tactic => `(tactic| repeat (first | exact keeps_refl _ _ | (refine keeps_setObj' ?_ (chgX_of (by assumption))) | (refine keeps_setObj_fresh ?_ (by jdisch)) | (refine keeps_alloc' ?_) | (refine keeps_grows' ?_ (growsK_elim (by assumption)))))

macro "closeXS_state" : tactic => `(tactic| (refine (finXS_ex (by assumption) (by assumption) (by assumption) (by keepsS_tac) ?_).1; hsimp; refine ⟨_, rfl, fun k h1 h2 => get_set_other h1, ⟨_, (get_set_other (by decide)).trans (by assumption), fileAtM_keeps' (by assumption) (by keepsS_tac) ((away_chgS _).mono (by decide))⟩, ⟨_, (get_set_other (by decide)).trans (by assumption), jRecAt_keeps' (by assumption) (by keepsS_tac) ((away_chgS _).mono (by decide))⟩, ⟨_, get_set_same, _, rfl, ?_⟩⟩; rw [status_text]; hsimp; status_close))

macro "closeXS_sep" : tactic => `(tactic| exact finX_sep (by assumption) (by assumption) (by assumption) (by keepsS_tac) ((away_chgS _).mono (by decide)) (by hsimp; try rfl) (fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2]))

macro "closeX_state" : tactic => `(tactic| (refine (finX_ex (by assumption) (by assumption) (by assumption) (by keepsX_tac) ?_).1; hsimp; refine ⟨_, rfl, fun k h1 h2 => get_set_other h1, ⟨_, (get_set_other (by decide)).trans (by assumption), fileAtM_upd' (by assumption) (by assumption) (by keepsX_tac) ((away_chgX _).mono (by decide)) (by hsimp; try rfl) (by fields_close) (by fields_close) (by fields_close) (by first | decide | exact (fileAtM_flags (by assumption) (by assumption)).2.2.1) (by fields_close)⟩, ⟨_, (get_set_other (by decide)).trans (by assumption), jRecAt_keeps' (by assumption) (by keepsX_tac) ((away_chgX _).mono (by decide))⟩, ⟨_, get_set_same, _, rfl, ?_⟩⟩; rw [status_text]; hsimp; status_close))

macro "closeX_sep" : tactic => `(tactic| exact finX_sep (by assumption) (by assumption) (by assumption) (by keepsX_tac) ((away_chgX _).mono (by decide)) (by hsimp; try rfl) (fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2]))

macro "closeX_area" : tactic => `(tactic| (refine area_rc (by assumption) (by assumption) (by assumption) (by keepsX_tac) (away_chgX _) (by hsimp; try rfl) (fun k h => get_set_other h) get_set_same ⟨_, rfl, ?_⟩; rw [stBytes_text]; hsimp; status_close))

/-- The record buffer after an XREFFILE read: the record's text, space-padded to 1000. -/
theorem xref_fldt {c d : List UInt8} (hc : c.length = 16) (hd : d.length = 34) :
    fixStr (fixStr (cp037Str c) 16 ++ fixStr (cp037Str d) 34) 1000 =
      cp037Str (intoBuf (Model.FdXreffileRec.encode [.str c, .str d])) := by
  have he : Model.FdXreffileRec.encode [.str c, .str d] = c ++ d := by
    simp [Schema.encode, Field.encode]
  rw [he, intoBuf_text (by simp [hc, hd]), fixStr_eq_self (s := cp037Str c) (n := 16) (by rw [cp037Str_length, hc]),
    fixStr_eq_self (s := cp037Str d) (n := 34) (by rw [cp037Str_length, hd]), cp037Str_append]

end EquivLean.Modernize.Cbstm03b.Java
