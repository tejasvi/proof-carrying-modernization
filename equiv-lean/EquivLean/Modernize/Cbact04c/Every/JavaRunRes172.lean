import EquivLean.Modernize.Cbact04c.Every.JavaRunRes148

/-!
# CBACT04C → Java, `run`: the disclosure group lookup (statements 172–179)

`findDisc` compares the group and type strings (CP037 texts, `cp037Str_inj`) and the category of
the disclosure group objects with the account's group and the record's type and category: its
first match is the model's (`discIdx_disc`, `discOf_eq`). `j196_of_copy`: the record copied, the
cut point 196.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## CP037 is injective -/

/-- The EBCDIC byte of a UTF-16 unit (the inverse of `cp037Unit`). -/
def cp037Inv (u : JChar) : UInt8 := (_root_.Cobol.Codepage.cp037Byte (Char.ofNat u.toNat)).getD 0

theorem cp037Inv_unit_fin : ∀ n : Fin 256, cp037Inv (cp037Unit (UInt8.ofNat n.val)) = UInt8.ofNat n.val := by
  decide +kernel

theorem cp037Inv_unit (b : UInt8) : cp037Inv (cp037Unit b) = b := by
  have h := cp037Inv_unit_fin ⟨b.toNat, b.toNat_lt⟩
  simpa using h

theorem cp037Unit_inj {a b : UInt8} (h : cp037Unit a = cp037Unit b) : a = b := by
  rw [← cp037Inv_unit a, ← cp037Inv_unit b, h]

theorem cp037Str_inj : ∀ {x y : List UInt8}, cp037Str x = cp037Str y → x = y
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cp037Str] at h
  | _ :: _, [], h => by simp [cp037Str] at h
  | _ :: _, _ :: _, h => by
    simp only [cp037Str, List.map_cons, List.cons.injEq] at h
    rw [cp037Unit_inj h.1, cp037Str_inj h.2]

/-! ## The disclosure group objects -/

theorem dCat_range {d : List FV} (hv : DisGroupRecord.Valid d) :
    0 ≤ Model.dCat d ∧ Model.dCat d < 10000 := by
  have r := holds_display rfl (valid_num hv (i := 2) (by decide) (fmt := {digits := 4})
    (by decide)).2
  simp only [Nat.reducePow] at r
  have a0 := Int.natAbs_eq (Model.numOf (d.getD 2 default))
  have q := r.2 trivial
  simp only [Model.dCat]
  omega

/-- The key of a valid disclosure group record object. -/
theorem discKeyOf_rec {σ : State} {v : Value} {d : List FV}
    (h : JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ v d) (hv : DisGroupRecord.Valid d) :
    discKeyOf σ v = some (cp037Str (Model.dGrp d), cp037Str (Model.dType d),
      BitVec.ofInt 64 (Model.dCat d)) := by
  obtain ⟨y, fs, rfl, hy, hf⟩ := jrec_obj h
  obtain ⟨gv, hg, hgs⟩ := jfield_str hf hv (i := 0) (by decide) (j := false) (by decide)
  obtain ⟨tv, ht, hts⟩ := jfield_str hf hv (i := 1) (by decide) (j := false) (by decide)
  have hc := jfield_num hf hv (i := 2) (by decide) (fmt := {digits := 4}) (by decide)
  rw [show (DisGroupRecord.fields.getD 0 default).jname = "disAcctGroupId" from rfl] at hg
  rw [show (DisGroupRecord.fields.getD 1 default).jname = "disTranTypeCd" from rfl] at ht
  rw [show (DisGroupRecord.fields.getD 2 default).jname = "disTranCatCd" from rfl] at hc
  simp only [discKeyOf, hy, hg, ht, hc, strOf, hgs, hts]
  rfl

theorem discArr_of {σ : State} {xs : List Value} {ds : List (List FV)}
    (h : Forall2 (JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ) xs ds)
    (hv : ∀ d ∈ ds, DisGroupRecord.Valid d) : DiscArr σ xs := by
  intro x hx
  obtain ⟨d, hd, hr⟩ := forall2_mem_left h x hx
  obtain ⟨y, fs, rfl, hy, hf⟩ := jrec_obj hr
  obtain ⟨gv, hg, hgs⟩ := jfield_str hf (hv d hd) (i := 0) (by decide) (j := false) (by decide)
  obtain ⟨tv, ht, hts⟩ := jfield_str hf (hv d hd) (i := 1) (by decide) (j := false) (by decide)
  have hc := jfield_num hf (hv d hd) (i := 2) (by decide) (fmt := {digits := 4}) (by decide)
  exact ⟨y, fs, gv, tv, _, _, _, rfl, hy, hg, hgs, ht, hts, hc⟩

/-- The model's lookup predicate and the Java comparison agree. -/
theorem disc_key_iff {σ : State} {v : Value} {d : List FV}
    (h : JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ v d) (hv : DisGroupRecord.Valid d)
    (grp ty : List UInt8) {cat : Int} (hc0 : 0 ≤ cat) (hc1 : cat < 10000) :
    discKeyOf σ v = some (cp037Str grp, cp037Str ty, BitVec.ofInt 64 cat) ↔
      (Model.dGrp d == grp && Model.dType d == ty && Model.dCat d == cat) = true := by
  rw [discKeyOf_rec h hv]
  have hr := dCat_range hv
  simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨cp037Str_inj h1, cp037Str_inj h2⟩,
      ofInt64_inj (by omega) (by omega) (by omega) (by omega) h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by rw [h1], by rw [h2], by rw [h3]⟩

/-- `findDisc`'s search over the disclosure groups is the model's. -/
theorem findIdx_disc {σ : State} (grp ty : List UInt8) {cat : Int} (hc0 : 0 ≤ cat)
    (hc1 : cat < 10000) :
    ∀ {xs : List Value} {ds : List (List FV)},
      Forall2 (JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ) xs ds →
      (∀ d ∈ ds, DisGroupRecord.Valid d) →
      xs.findIdx? (fun x => decide (discKeyOf σ x = some (cp037Str grp, cp037Str ty,
        BitVec.ofInt 64 cat))) =
        ds.findIdx? (fun d => Model.dGrp d == grp && Model.dType d == ty && Model.dCat d == cat)
  | [], [], .nil, _ => rfl
  | _ :: _, d :: _, .cons hxd hrest, hv => by
    rw [List.findIdx?_cons, List.findIdx?_cons,
      findIdx_disc grp ty hc0 hc1 hrest (fun d hd => hv d (List.mem_cons_of_mem _ hd))]
    have hk := disc_key_iff hxd (hv d (List.mem_cons_self ..)) grp ty hc0 hc1
    by_cases hm : (Model.dGrp d == grp && Model.dType d == ty && Model.dCat d == cat) = true
    · simp only [hk.2 hm, decide_true, hm, ↓reduceIte]
    · have hn : ¬ discKeyOf σ _ = some (cp037Str grp, cp037Str ty, BitVec.ofInt 64 cat) :=
        fun h => hm (hk.1 h)
      simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.not_eq_true] at hm
      simp [hm]

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- **The position `findDisc` returns**: the model's first match. -/
theorem discIdx_disc {σ : State} {a gs ts : Addr} {et : JType} {xs : List Value}
    {ds : List (List FV)} {grp ty : List UInt8} {cat : Int}
    (ha : σ.heap a = some (.array et xs)) (hgs : σ.heap gs = some (.str (cp037Str grp)))
    (hts : σ.heap ts = some (.str (cp037Str ty)))
    (h : Forall2 (JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ) xs ds)
    (hv : ∀ d ∈ ds, DisGroupRecord.Valid d) (hc0 : 0 ≤ cat) (hc1 : cat < 10000) {jd : Nat}
    (hjd : ds.findIdx? (fun d => Model.dGrp d == grp && Model.dType d == ty && Model.dCat d == cat) =
      some jd) :
    discIdx σ a gs ts (BitVec.ofInt 64 cat) = BitVec.ofNat 32 jd := by
  simp only [discIdx, ha, hgs, hts, findIdx_disc grp ty hc0 hc1 h hv, hjd]

theorem discOf_eq {g : G} {s : Model.St} {t : List FV} {jd : Nat}
    (hjd : g.discs.findIdx? (fun d => Model.dGrp d == Model.aGrp s.acct && Model.dType d == Model.tType t &&
      Model.dCat d == Model.tCat t) = some jd) :
    ∃ h : jd < g.discs.length, discOf g s t = g.discs[jd] := by
  obtain ⟨hjl, hp, hprev⟩ := List.findIdx?_eq_some_iff_getElem.1 hjd
  refine ⟨hjl, ?_⟩
  simp only [discOf]
  rw [Model.find?_eq_getElem _ _ jd hjl hp (fun k hk => by simpa using hprev k hk), Option.getD_some]

/-- **The disclosure group record copied** (statements 172–179): the cut point 196. -/
theorem j196_of_copy {g : G} {σ0 σ σ1 : State} {fr' : Frame} {i : I32} {hp : Hp} {y : Addr}
    {acctV xrefV lastV : Value} {xs : List Value} {jd : Nat} {dk dc : Addr}
    {fsc : List (FieldKey × Value)}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt)
    (hstop : (g.stE i.toInt.toNat).stop = false) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).total)))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).k)))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV) (f7 : fr'.get 7 = some (.ref dc))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      acctV xrefV lastV))
    (hds : Hide (Forall2 (JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ) xs g.discs))
    (hjd : g.discs.findIdx? (fun d =>
      Model.dGrp d == Model.aGrp (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct &&
      Model.dType d == Model.tType (g.trec i.toInt.toNat) &&
      Model.dCat d == Model.tCat (g.trec i.toInt.toNat)) = some jd)
    (hdk : xs[jd]? = some (.ref dk))
    (hdc : σ1.heap dc = some (.plain "Cbact04c$DisGroupRecord" fsc))
    (hkc : ∀ key ∈ keysDC, Fields.get fsc ("Cbact04c$DisGroupRecord", key) =
      Fields.get (fieldsOf σ dk) ("Cbact04c$DisGroupRecord", key))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) (hdne : ∀ d ∈ g.discs, d ≠ []) :
    J196 g g.args σ0 fr' σ1 := by
  obtain ⟨hjl, hdisc⟩ := discOf_eq hjd
  have hnm : grpMissing g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      (g.trec i.toInt.toNat) = false := by
    unfold grpMissing
    rw [findRateO_eq, Option.isNone_map, Bool.eq_false_iff]
    intro h
    rw [Option.isNone_iff_eq_none] at h
    apply hdne _ (List.getElem_mem hjl)
    rw [← hdisc]
    unfold discOf
    rw [h]
    rfl
  have hsel : sel g i.toInt.toNat = stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat) := by
    unfold sel selD
    rw [hnm]
    rfl
  have hdd : discD g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      (g.trec i.toInt.toNat) =
      discOf g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat) := by
    unfold discD
    rw [hnm]
    rfl
  have hf := Hide.elim hds
  have hxl := Forall2.length_eq hf
  have hjx : jd < xs.length := by omega
  have hrel := forall2_getElem hf jd hjx
  rw [List.getElem?_eq_getElem hjx] at hdk
  have hdk' : xs[jd] = .ref dk := Option.some.inj hdk
  rw [hdk'] at hrel
  obtain ⟨x0, fsk, hx0, hdkh, -⟩ := id hrel
  cases hx0
  have hrc : JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ1 (.ref dc)
      (discOf g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat)) := by
    rw [hdisc]
    rw [fieldsOf_eq hdkh] at hkc
    exact jrecAt_copy hrel hdkh hdc (same_keys disGroupRecord_jnames hkc) (strKeep_of_grows hg)
  refine ⟨i, hp, .ref y, acctV, xrefV, lastV, .ref dc, ?_⟩
  rw [hsel, hdd]
  exact ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5,
    Hide.intro (jrecAt_grows hg (Hide.elim htcb)), hstop⟩, f3, f12, f14, f25, f16, f17, f7,
    Hide.intro (loopHeap_grows (Hide.elim hheap) hg hi), Hide.intro hrc⟩

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

theorem stSel_lastId (xrefs : List (List FV)) (s : Model.St) (t : List FV) :
    (stSel xrefs s t).lastId = some (Model.tAcct t) := by
  unfold stSel
  split
  · next h => simpa [disp1] using h
  · rfl

/-- The disclosure group array, from the inputs, in a state grown from the entry state. -/
theorem discArr_of_pre {g : G} {args : List Value} {σ0 σ : State} (hpre : RunPreG g args σ0)
    (hg : Grows σ0 σ) : ∃ et xs, σ.heap g.a4 = some (.array et xs) ∧ xs.length < 2147483648 ∧
      Forall2 (JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ) xs g.discs ∧
      ∀ d ∈ g.discs, DisGroupRecord.Valid d := by
  obtain ⟨-, ⟨b1, b2, b3, b4, q1, c1, hargs, -, -, -, ⟨et4, xs4, h4, hb4, hp4⟩, -, -, -, -, -, -,
    hv4, -, -⟩, -⟩ := hpre
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨-, -, -, rfl, -⟩ := hargs
  exact ⟨et4, xs4, heap_of_grows hg h4, hb4, forall2_mono (fun _ _ h => jrecAt_grows hg h) hp4, hv4⟩

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

theorem jrecAt_ne_nil {s : Schema} {cls : ClassName} {σ : State} {v : Value} {vals : List FV}
    (h : JRecAt s cls σ v vals) (hs : s.fields ≠ []) : vals ≠ [] := by
  obtain ⟨x, fs, -, -, hf⟩ := h
  intro e
  subst e
  have hl := Forall2.length_eq hf
  exact hs (List.eq_nil_of_length_eq_zero (by simpa using hl))

/-- The account of the record exists (it was found: the account part holds a record). -/
theorem hex_of_found {g : G} (hin : InFacts g) {n : Nat} (hs : (g.stE n).stop = false)
    (hacc : (stSel g.xrefs (g.st n) (g.trec n)).acct ≠ []) :
    ∃ a ∈ g.accts, Model.aId a = Model.tAcct (g.trec n) := by
  have hst := stInv_st hin n hs
  by_cases h : (g.st n).lastId = some (Model.tAcct (g.trec n))
  · obtain ⟨-, -, -, hcur, -⟩ := hst
    exact (hcur _ h).2.2.1
  · have hsel : (stSel g.xrefs (g.st n) (g.trec n)).acct =
        Model.findAcct (stRw (g.st n) (g.trec n)).accts (Model.tAcct (g.trec n)) := by
      unfold stSel
      rw [if_neg h]
      rfl
    rw [hsel] at hacc
    have hf := findAcctO_of_ne hacc
    unfold Model.findAcctO at hf
    have hmem := List.mem_of_find?_eq_some hf
    have hid := List.find?_some hf
    simp only [beq_iff_eq] at hid
    exact exists_aId_of_map (stRw_ids hst (g.trec n)).symm ⟨_, hmem, hid⟩

end EquivLean.Modernize.Cbact04c.Java
