import EquivLean.Modernize.Cbact04c.Every.JavaRunRes172

/-!
# CBACT04C → Java, `run`: the interest rate (statements 196–198)

`st_succ_eq`: the model state after record `i` is the interest part `stFin` at the rate of the
copied disclosure group record, after the account part `stSel`. `j85_of`: the loop head for the
next record (cut point 85).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem trec_eq {g : G} {n : Nat} (hn : n < g.tcat.length) : g.trec n = g.tcat[n] := by
  simp [G.trec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

/-- **One record of the model**, when its lookups succeed (in the phases of the loop body). -/
theorem st_succ_eq (g : G) {n : Nat} (hn : n < g.tcat.length) (hs : (g.stE n).stop = false)
    (hacc : (stSel g.xrefs (g.st n) (g.trec n)).acct ≠ [])
    (hxr : (stSel g.xrefs (g.st n) (g.trec n)).xref ≠ [])
    (hd : discD g (stSel g.xrefs (g.st n) (g.trec n)) (g.trec n) ≠ []) :
    g.st (n + 1) = stFin g.parm g.clk (rateOf g n) (sel g n) (g.trec n) ∧
      (g.stE (n + 1)).stop = false := by
  have e := G.stE_succ g hn
  rw [← trec_eq hn] at e
  have h := stepE_found g (g.stE n) (g.trec n) hs hacc hxr hd
  refine ⟨?_, by rw [e]; exact h.2⟩
  show stOf (g.stE (n + 1)) = _
  rw [e]
  exact h.1

/-- **The loop head for the next record** (cut point 85). -/
theorem j85_of {g : G} {σ0 σ : State} {fr' : Frame} {i : I32} {hp : Hp}
    {acctV xrefV lastV : Value} (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt)
    (hlen : g.tcat.length < 2147483647) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32)))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (g.st (i.toInt.toNat + 1)).total)))
    (f3 : fr'.get 3 = some (.int 0#32)) (hsome : (g.st (i.toInt.toNat + 1)).lastId.isSome)
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st (i.toInt.toNat + 1)).k)))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV) (f4 : fr'.get 4 = some (.int 0#32))
    (f5 : fr'.get 5 = some (.int 0#32))
    (hheap : Hide (LoopHeap g σ0 σ hp (g.st (i.toInt.toNat + 1)) acctV xrefV lastV))
    (hstop1 : (g.stE (i.toInt.toNat + 1)).stop = false) :
    J85 g g.args σ0 fr' σ := by
  have hi1 := i32_toInt_add_one i hi0 (by omega)
  have hn1 : (i + 1#32).toInt.toNat = i.toInt.toNat + 1 := by omega
  refine ⟨i + 1#32, hp, acctV, xrefV, lastV, by omega, by omega, hlocs, f22, ?_, ?_, ?_, f25, f16,
    f17, f4, f5, ?_, ?_⟩
  · rw [hn1]; exact f12
  · rw [hn1, hsome]; exact f3
  · rw [hn1]; exact f14
  · rw [hn1]; exact hheap
  · rw [hn1]; exact hstop1

/-- The interest rate field of a valid disclosure group record object. -/
theorem disRate_field {σ : State} {v : Value} {d : List FV}
    (h : JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ v d) (hv : DisGroupRecord.Valid d) :
    ∃ x fs, v = .ref x ∧ σ.heap x = some (.plain "Cbact04c$DisGroupRecord" fs) ∧
      Fields.get fs ("Cbact04c$DisGroupRecord", "disIntRate") =
        some (.long (BitVec.ofInt 64 (Model.dRate d))) ∧
      -1000000 < Model.dRate d ∧ Model.dRate d < 1000000 := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := jrec_obj h
  have hk := jfield_num hf hv (i := 3) (by decide) (fmt := {digits := 6, scale := 2, signed := true})
    (by decide)
  rw [show (DisGroupRecord.fields.getD 3 default).jname = "disIntRate" from rfl] at hk
  have r := holds_display rfl (valid_num hv (i := 3) (by decide)
    (fmt := {digits := 6, scale := 2, signed := true}) (by decide)).2
  simp only [Nat.reducePow] at r
  have a0 := Int.natAbs_eq (Model.numOf (d.getD 3 default))
  exact ⟨x, fs, rfl, hx, hk, by simp only [Model.dRate]; omega, by simp only [Model.dRate]; omega⟩

/-- The disclosure group record of the account part is a record of the input. -/
theorem discOf_valid {g : G} (hv : ∀ d ∈ g.discs, DisGroupRecord.Valid d) (s : Model.St)
    (t : List FV) (hex : ∃ jd, g.discs.findIdx? (fun d => Model.dGrp d == Model.aGrp s.acct &&
      Model.dType d == Model.tType t && Model.dCat d == Model.tCat t) = some jd) :
    DisGroupRecord.Valid (discOf g s t) := by
  obtain ⟨jd, hjd⟩ := hex
  obtain ⟨hjl, hd⟩ := discOf_eq hjd
  rw [hd]
  exact hv _ (List.getElem_mem hjl)

/-! ## The selected state: its fields, its lookups -/

theorem selD_acct (g : G) (s : Model.St) (t : List FV) : (selD g s t).acct = s.acct := by
  unfold selD; split <;> rfl
theorem selD_xref (g : G) (s : Model.St) (t : List FV) : (selD g s t).xref = s.xref := by
  unfold selD; split <;> rfl
theorem selD_lastId (g : G) (s : Model.St) (t : List FV) : (selD g s t).lastId = s.lastId := by
  unfold selD; split <;> rfl
theorem selD_total (g : G) (s : Model.St) (t : List FV) : (selD g s t).total = s.total := by
  unfold selD; split <;> rfl
theorem selD_k (g : G) (s : Model.St) (t : List FV) : (selD g s t).k = s.k := by
  unfold selD; split <;> rfl

/-- The account part found its account and cross-reference (they are objects of the loop heap). -/
theorem found_of_loopHeap {g : G} {σ0 σ : State} {h : Hp} {n : Nat} {acctV xrefV lastV : Value}
    (hL : LoopHeap g σ0 σ h (sel g n) acctV xrefV lastV) :
    (stSel g.xrefs (g.st n) (g.trec n)).acct ≠ [] ∧ (stSel g.xrefs (g.st n) (g.trec n)).xref ≠ [] := by
  obtain ⟨-, ha, hx, -, -⟩ := hL
  have hsome : (sel g n).lastId.isSome := by
    unfold sel
    rw [selD_lastId, stSel_lastId]
    rfl
  have h1 := jrecAt_ne_nil (ha hsome) (by decide)
  have h2 := jrecAt_ne_nil (hx hsome) (by decide)
  unfold sel at h1 h2
  rw [selD_acct] at h1
  rw [selD_xref] at h2
  exact ⟨h1, h2⟩

theorem dRate_nil : Model.dRate [] = 0 := rfl

/-- A nonzero rate was read from a disclosure record. -/
theorem discD_ne_of_rate {g : G} {n : Nat} (hr : rateOf g n ≠ 0) :
    discD g (stSel g.xrefs (g.st n) (g.trec n)) (g.trec n) ≠ [] := by
  intro e
  apply hr
  unfold rateOf
  rw [e]
  rfl

theorem getD_find_mem {l : List (List FV)} {p : List FV → Bool} (h : (l.find? p).getD [] ≠ []) :
    (l.find? p).getD [] ∈ l := List.mem_of_find?_eq_some (find?_getD_ne h)

/-- The disclosure record the rate is read from is a record of the file. -/
theorem discD_valid {g : G} (hv : ∀ d ∈ g.discs, DisGroupRecord.Valid d) {s : Model.St}
    {t : List FV} (hne : discD g s t ≠ []) : DisGroupRecord.Valid (discD g s t) := by
  unfold discD at *
  by_cases hm : grpMissing g s t = true
  · rw [if_pos hm] at hne ⊢
    exact hv _ (getD_find_mem hne)
  · rw [if_neg hm] at hne ⊢
    exact hv _ (getD_find_mem hne)

/-- The account object of the selected state (from the loop heap of `sel`). -/
theorem loopHeap_acct_sel {g : G} {σ0 σ : State} {h : Hp} {n : Nat} {acctV xrefV lastV : Value}
    (hL : LoopHeap g σ0 σ h (sel g n) acctV xrefV lastV) :
    JRecAt AccountRecord "Cbact04c$AccountRecord" σ acctV (stSel g.xrefs (g.st n) (g.trec n)).acct := by
  obtain ⟨-, ha, -, -, -⟩ := hL
  have hs : (sel g n).lastId.isSome := by
    unfold sel
    rw [selD_lastId, stSel_lastId]
    rfl
  have h1 := ha hs
  unfold sel at h1
  rwa [selD_acct] at h1

/-- The cross-reference object of the selected state. -/
theorem loopHeap_xref_sel {g : G} {σ0 σ : State} {h : Hp} {n : Nat} {acctV xrefV lastV : Value}
    (hL : LoopHeap g σ0 σ h (sel g n) acctV xrefV lastV) :
    JRecAt CardXrefRecord "Cbact04c$CardXrefRecord" σ xrefV (stSel g.xrefs (g.st n) (g.trec n)).xref := by
  obtain ⟨-, -, hx, -, -⟩ := hL
  have hs : (sel g n).lastId.isSome := by
    unfold sel
    rw [selD_lastId, stSel_lastId]
    rfl
  have h1 := hx hs
  unfold sel at h1
  rwa [selD_xref] at h1

end EquivLean.Modernize.Cbact04c.Java
