import EquivLean.Modernize.Cbact04c.Every.JavaRunModelStep

/-!
# CBACT04C → Java: what holds of every model state of the fold

`StInv g s`: the account table keeps its ids and groups and its records stay valid; once a record
was read, the current account and cross-reference are the lookups of the last account id, which is
the id of an account and below `10^11`; the total stays below `10^11` and the suffix below `10^6`.
`stInv_st`: it holds of `g.st n` for every `n`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- What holds of every model state along the fold. -/
def StInv (g : G) (s : Model.St) : Prop :=
  s.accts.map Model.aId = g.accts.map Model.aId ∧
  s.accts.map Model.aGrp = g.accts.map Model.aGrp ∧
  (∀ a ∈ s.accts, AccountRecord.Valid a) ∧
  (∀ id, s.lastId = some id →
    s.acct = Model.findAcct s.accts id ∧ s.xref = Model.findXref g.xrefs id ∧
    (∃ a ∈ g.accts, Model.aId a = id) ∧ 0 ≤ id ∧ id < 100000000000) ∧
  -100000000000 < s.total ∧ s.total < 100000000000 ∧ s.k < 1000000

/-! ## Lists -/

/-- Replacing the first account with id `id` by `x` keeps `f` of the table when `x` agrees with
the account found. -/
theorem map_replaceFirst_findAcct {β : Type} (f : List FV → β) (l : List (List FV)) (id : Int)
    (x : List FV) (hex : ∃ a ∈ l, Model.aId a = id) (hx : f x = f (Model.findAcct l id)) :
    (Model.replaceFirst (fun a => Model.aId a == id) x l).map f = l.map f := by
  obtain ⟨a, ha, haid⟩ := hex
  obtain ⟨i, hi, hp, hj⟩ := Model.exists_first (fun a => Model.aId a == id) l ⟨a, ha, by simpa using haid⟩
  rw [Model.replaceFirst_eq_set _ _ l i hi hp hj]
  have hfind : Model.findAcct l id = l[i] := by
    simp only [Model.findAcct, Model.find?_eq_getElem (fun a => Model.aId a == id) l i hi hp hj,
      Option.getD_some]
  rw [hfind] at hx
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_set]
  split
  · next h => subst h; exact hx
  · rfl

theorem exists_aId_of_map {l l' : List (List FV)} (h : l.map Model.aId = l'.map Model.aId) {id : Int}
    (hex : ∃ a ∈ l', Model.aId a = id) : ∃ a ∈ l, Model.aId a = id := by
  obtain ⟨a, ha, rfl⟩ := hex
  have : Model.aId a ∈ l.map Model.aId := by rw [h]; exact List.mem_map_of_mem ha
  obtain ⟨b, hb, he⟩ := List.mem_map.1 this
  exact ⟨b, hb, he⟩

/-! ## Valid records -/

theorem holds_of_display {fmt : Cobol.NumFmt} (hu : fmt.usage = .display) {v : Int}
    (h1 : v.natAbs < 10 ^ fmt.digits) (h2 : fmt.signed = false → 0 ≤ v) : fmt.Holds {} v := by
  unfold Cobol.NumFmt.Holds Cobol.NumFmt.fullBinary
  simp only [hu]
  exact ⟨h1, h2⟩

/-- A numeric field of a valid record set to another number its picture holds. -/
theorem valid_set_num {s : Schema} {vals : List FV} (hv : s.Valid vals) {i : Nat}
    (hi : i < s.fields.length) {fmt : Cobol.NumFmt}
    (hk : (s.fields.getD i default).desc.kind = .num fmt) {v : Int} (hh : fmt.Holds {} v) :
    s.Valid (vals.set i (.num v)) := by
  have h := Forall2.getD hv i hi
  have hw := (valid_num hv hi hk).1
  rw [hw] at h
  obtain ⟨fmt', hk', hd1, hd2, -, hb⟩ := h
  rw [hk] at hk'
  cases hk'
  have hf : Field.Valid (s.fields.getD i default) (.num v) := ⟨fmt, hk, hd1, hd2, hh, hb⟩
  have := forall2_set hf i hv
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.set_getElem_self] at this

/-- **The posted account is valid.** -/
theorem valid_posted {a : List FV} (ha : AccountRecord.Valid a) {total : Int}
    (h1 : -100000000000 < total) (h2 : total < 100000000000) :
    AccountRecord.Valid (Model.posted a total) := by
  have hm := Int.tmod_lt_of_pos (Model.aBal a + total) (b := 10 ^ 12) (by decide)
  have hm' := Int.lt_tmod_of_pos (Model.aBal a + total) (b := 10 ^ 12) (by decide)
  unfold Model.posted
  refine valid_set_num (valid_set_num (valid_set_num ha (i := 2) (by decide)
    (fmt := {digits := 12, scale := 2, signed := true}) (by decide) ?_) (i := 8) (by decide)
    (fmt := {digits := 12, scale := 2, signed := true}) (by decide) ?_) (i := 9) (by decide)
    (fmt := {digits := 12, scale := 2, signed := true}) (by decide) ?_
  · refine holds_of_display rfl ?_ (fun h => by cases h)
    simp only [Nat.reducePow]
    omega
  · exact holds_of_display rfl (by decide) (fun h => by cases h)
  · exact holds_of_display rfl (by decide) (fun h => by cases h)

/-- The ranges of a valid category record's account id. -/
theorem tAcct_range {t : List FV} (hv : TranCatBalRecord.Valid t) :
    0 ≤ Model.tAcct t ∧ Model.tAcct t < 100000000000 := by
  have r0 := holds_display rfl (valid_num hv (i := 0) (by decide) (fmt := {digits := 11})
    (by decide)).2
  simp only [Nat.reducePow] at r0
  have a0 := Int.natAbs_eq (Model.numOf (t.getD 0 default))
  have q0 := r0.2 trivial
  simp only [Model.tAcct]
  omega

/-! ## The invariant along the fold -/

theorem stInv_init (g : G) (hv : ∀ a ∈ g.accts, AccountRecord.Valid a) :
    StInv g (Model.init g.accts) := by
  refine ⟨rfl, rfl, hv, ?_, by simp [Model.init], by simp [Model.init], by simp [Model.init]⟩
  intro id h
  simp [Model.init] at h

theorem stInv_disp1 {g : G} {s : Model.St} (h : StInv g s) (t : List FV) : StInv g (disp1 s t) := h

theorem stInv_stSel {g : G} {s : Model.St} (h : StInv g s) {t : List FV}
    (hv : TranCatBalRecord.Valid t) (hex : ∃ a ∈ g.accts, Model.aId a = Model.tAcct t) :
    StInv g (stSel g.xrefs s t) := by
  obtain ⟨hid, hgrp, hval, hcur, ht1, ht2, hk⟩ := h
  unfold stSel
  split
  · exact ⟨hid, hgrp, hval, hcur, ht1, ht2, hk⟩
  · -- the new account: the previous one rewritten (if any), the new one and its xref read
    have hr := tAcct_range hv
    -- the table after the rewrite keeps ids, groups, validity
    have hrw : (stRw s t).accts.map Model.aId = g.accts.map Model.aId ∧
        (stRw s t).accts.map Model.aGrp = g.accts.map Model.aGrp ∧
        (∀ a ∈ (stRw s t).accts, AccountRecord.Valid a) := by
      unfold stRw disp1
      cases hl : s.lastId with
      | none => exact ⟨hid, hgrp, hval⟩
      | some id =>
        obtain ⟨hacc, -, hexg, -, -⟩ := hcur id hl
        have hex' := exists_aId_of_map hid hexg
        have hspec := Model.findAcct_spec s.accts id hex'
        have hacid : Model.aId s.acct = id := by rw [hacc]; exact hspec.2
        simp only [Option.isSome_some, ↓reduceIte, hacid]
        refine ⟨?_, ?_, ?_⟩
        · rw [map_replaceFirst_findAcct _ _ _ _ hex' (by rw [Model.aId_posted, hacc])]; exact hid
        · rw [map_replaceFirst_findAcct _ _ _ _ hex' (by rw [Model.aGrp_posted, hacc])]; exact hgrp
        · intro a ha
          rcases Model.mem_replaceFirst _ _ _ a ha with rfl | ha
          · exact valid_posted (hval _ (hacc ▸ hspec.1)) ht1 ht2
          · exact hval a ha
    obtain ⟨h1, h2, h3⟩ := hrw
    have hk' : (stRw s t).k < 1000000 := by
      unfold stRw disp1
      cases hl : s.lastId <;> simp [hk]
    refine ⟨h1, h2, h3, ?_, by simp [stAcct], by simp [stAcct], hk'⟩
    intro id hid'
    simp only [stAcct, Option.some.injEq] at hid'
    subst hid'
    exact ⟨rfl, rfl, hex, hr.1, hr.2⟩

theorem stInv_stFin {g : G} {s : Model.St} (h : StInv g s) (parm clk : List UInt8) (rate : Int)
    (t : List FV) : StInv g (stFin parm clk rate s t) := by
  obtain ⟨hid, hgrp, hval, hcur, ht1, ht2, hk⟩ := h
  unfold stFin
  split
  · exact ⟨hid, hgrp, hval, hcur, ht1, ht2, hk⟩
  · have hm := Int.tmod_lt_of_pos (s.total + Int.tmod (Int.tdiv (Model.tBal t * rate) 120000) (10 ^ 11))
      (b := 10 ^ 11) (by decide)
    have hm' := Int.lt_tmod_of_pos (s.total + Int.tmod (Int.tdiv (Model.tBal t * rate) 120000) (10 ^ 11))
      (b := 10 ^ 11) (by decide)
    refine ⟨hid, hgrp, hval, hcur, ?_, ?_, Nat.mod_lt _ (by decide)⟩ <;> simp only [Nat.reducePow] at hm hm' ⊢ <;> omega

/-- The facts of the inputs the fold needs (from `RunIn`). -/
structure InFacts (g : G) : Prop where
  tcat_valid : ∀ t ∈ g.tcat, TranCatBalRecord.Valid t
  accts_valid : ∀ a ∈ g.accts, AccountRecord.Valid a
  dom : Every.Domain g.tcat g.xrefs g.accts g.discs g.link
  discs_ne : ∀ d ∈ g.discs, d ≠ []

end EquivLean.Modernize.Cbact04c.Java
