import EquivLean.Modernize.Cbact04c.RustRun1

/-!
# CBACT04C → Rust: the glue to the model's field values, and the model's invariant

* CP037 round trips (`decide +kernel`): `cp037Code ∘ ebcdicOfLatin1 = id` on `0 ..= 255`,
  `ebcdicOfLatin1 ∘ latin1OfEbcdic = id`; so the EBCDIC bytes of Rust bytes (`ebc`) determine them;
* a record's display line is its text (`tcatLine_text`), the transaction built is `Model.tranVals`
  (`tranOf_vals`), the account rewritten is `Model.posted` (`postedR_vals`);
* the Rust searches against the model's `find?` lookups (`find_map_getD`, `replaceFirst_map`);
* `MInv`: what the model's state keeps (the table's ids and groups; the current account and
  cross-reference are the lookups of the last id) and `minv_step`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-! ## CP037 round trips -/

theorem cp037_rt : ∀ n : Fin 256, cp037Code (ebcdicOfLatin1 n.val) = n.val := by
  decide +kernel

theorem latin_rt_fin : ∀ n : Fin 256,
    ebcdicOfLatin1 (latin1OfEbcdic (UInt8.ofNat n.val)) = UInt8.ofNat n.val := by
  decide +kernel

theorem latin_rt (b : UInt8) : ebcdicOfLatin1 (latin1OfEbcdic b) = b := by
  have h := latin_rt_fin ⟨b.toNat, b.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  exact h

/-- The EBCDIC byte of a Rust byte. -/
abbrev ebc (u : U8) : UInt8 := ebcdicOfLatin1 u.val

theorem cp037_ebc (u : U8) : cp037Code (ebc u) = u.val :=
  cp037_rt ⟨u.val, by have := u.hBounds; simpa using this⟩

/-- The Latin-1 bytes of an alphanumeric field are the CP037 text of its EBCDIC bytes. -/
theorem latin1_text (l : List U8) : (l.map ebc).map cp037Code = l.map UScalar.val := by
  rw [List.map_map]
  exact List.map_congr_left fun u _ => cp037_ebc u

theorem ebc_inj {u v : U8} (h : ebc u = ebc v) : u = v := by
  apply UScalar.eq_of_val_eq
  rw [← cp037_ebc u, ← cp037_ebc v, h]

theorem map_ebc_inj {l1 l2 : List U8} : l1.map ebc = l2.map ebc ↔ l1 = l2 :=
  ⟨fun h => List.map_injective_iff.2 (fun _ _ => ebc_inj) h, fun h => h ▸ rfl⟩

theorem cp037Code_inj {a b : UInt8} (h : cp037Code a = cp037Code b) : a = b := by
  have ha := latin_rt a
  have hb := latin_rt b
  have e : latin1OfEbcdic a = latin1OfEbcdic b := h
  rw [← ha, ← hb, e]

theorem map_cp037_inj {l1 l2 : List UInt8} (h : l1.map cp037Code = l2.map cp037Code) : l1 = l2 :=
  List.map_injective_iff.2 (fun _ _ => cp037Code_inj) h

/-! ## Digits -/

theorem digs_val (n v : Nat) : (digs n v).map UScalar.val = zpad n v := by
  simp only [digs, zpad, List.map_map]
  apply List.map_congr_left
  intro e he
  have := Cobol.Digits.toDigits_lt (by decide) n v e he
  simp only [Function.comp_apply]
  rw [byt_val _ (by omega)]

theorem sdigs_val (n : Nat) (v : Int) :
    (sdigs n v).map UScalar.val =
      zpad (n - 1) (v.natAbs / 10) ++ [overpunch (decide (v < 0)) (v.natAbs % 10)] := by
  simp only [sdigs, List.map_append, digs_val, List.map_cons, List.map_nil]
  rw [byt_val _ (overpunch_lt _ _ (Nat.mod_lt _ (by norm_num)))]

/-- The EBCDIC digits of an unsigned DISPLAY field are the EBCDIC bytes of its Latin-1 digits. -/
theorem digs_ebc {fmt : NumFmt} (hu : fmt.usage = .display) (hs : fmt.signed = false)
    (hd : 0 < fmt.digits) (v : Int) :
    (digs fmt.digits v.natAbs).map ebc = encodeNum {} fmt v := by
  apply map_cp037_inj
  rw [latin1_text, digs_val, text_unsigned hu hs hd]

/-! ## A record's display line is its text -/

theorem tcatLine_text (r : cbact04c_t.TranCatBalRecord) :
    (tcatLine r).map UScalar.val = Model.TranCatBalRecord.textS (TranCatBalRecord.vals r) := by
  show _ = TranCatBalRecord.textS (TranCatBalRecord.vals r)
  simp only [tcatLine, List.map_append, digs_val, sdigs_val, Schema.textS, TranCatBalRecord.vals,
    List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, fieldTextS, latin1_text, List.append_nil, List.append_assoc,
    Bool.false_eq_true, _root_.ite_false, _root_.ite_true, List.singleton_append]

/-! ## The account rewritten -/

theorem tmod12_val (x : Int) :
    (⟨BitVec.ofInt _ (Int.tmod x (10 ^ 12))⟩ : I64).val = Int.tmod x (10 ^ 12) := by
  have hb : (Int.tmod x (10 ^ 12)).natAbs < 10 ^ 12 := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_lt _ (by norm_num)
  show (BitVec.ofInt _ (Int.tmod x (10 ^ 12))).toInt = _
  rw [BitVec.toInt_ofInt]
  simp only [IScalarTy.I64_numBits_eq]
  generalize Int.tmod x (10 ^ 12) = y at hb ⊢
  apply Int.bmod_eq_of_le <;> push_cast <;> omega

theorem postedR_vals (a : cbact04c_t.AccountRecord) (total : I64) :
    AccountRecord.vals (postedR a total) = Model.posted (AccountRecord.vals a) total.val := by
  simp only [postedR, AccountRecord.vals, Model.posted, Model.aBal, Model.numOf, tmod12_val,
    List.getD_cons_succ, List.getD_cons_zero, List.set_cons_succ, List.set_cons_zero, isz_lit_val]

/-! ## The transaction written -/

theorem getD_ebc (c : List U8) (k : Nat) :
    ebc (c.getD k 0#u8) = ebcdicOfLatin1 ((c.map UScalar.val).getD k 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases c[k]? <;> rfl

theorem tsList_ebc (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hclk : clock.val.map (·.val) = rustLine clk) (hlen : clk.length = 21) :
    (tsList clock.val).map ebc = CardDemo.Cbact04c.db2ts clk := by
  have key : ∀ k, ebc (clock.val.getD k 0#u8) = ebcdicOfLatin1 ((rustLine clk).getD k 0) := by
    intro k; rw [getD_ebc]; congr 2
  simp only [tsList, List.map_cons, List.map_nil, key]
  match clk, hlen with
  | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20], _ =>
    have e45 : ebc 45#u8 = 96 := by decide +kernel
    have e46 : ebc 46#u8 = 75 := by decide +kernel
    have e48 : ebc 48#u8 = 240 := by decide +kernel
    simp only [rustLine, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero,
      latin_rt, CardDemo.Cbact04c.db2ts, e45, e46, e48, List.take_succ_cons, List.drop_succ_cons,
      List.take_zero, List.cons_append, List.nil_append, List.drop_zero]

theorem tranOf_vals (prev : cbact04c_t.TranRecord) (parm : Std.Array U8 10#usize)
    (suffix acct amt : I64) (card : Std.Array U8 16#usize) (clock : Std.Array U8 21#usize)
    (clk : List UInt8) (hk0 : 0 ≤ suffix.val)
    (hdesc : prev.tran_desc.val.drop 24 = List.replicate 76 32#u8)
    (hfill : prev.filler1.val = List.replicate 20 32#u8)
    (hclk : clock.val.map (·.val) = rustLine clk) (hlen : clk.length = 21) :
    TranRecord.vals (tranOf prev parm suffix acct amt card clock) =
      Model.tranVals (parm.val.map ebc) clk suffix.val.toNat acct.val (card.val.map ebc) amt.val := by
  have h6 := digs_ebc (fmt := CardDemo.Cbact04c.WS_TRANID_SUFFIX.fmt) rfl rfl (by decide) suffix.val
  have h11 := digs_ebc (fmt := CardDemo.Cbact04c.ACCT_ID.fmt) rfl rfl (by decide) acct.val
  have hd6 : CardDemo.Cbact04c.WS_TRANID_SUFFIX.fmt.digits = 6 := rfl
  have hd11 : CardDemo.Cbact04c.ACCT_ID.fmt.digits = 11 := rfl
  rw [hd6] at h6
  rw [hd11] at h11
  have hk : ((suffix.val.toNat : Nat) : Int) = suffix.val := Int.toNat_of_nonneg hk0
  simp only [TranRecord.vals, tranOf, Model.tranVals, Std.Array.from_val, List.map_append, h6, h11,
    hk, hdesc, hfill, tsArr, tsList_ebc clock clk hclk hlen, Std.Array.make, Std.Array.repeat_val,
    isz_lit_val, List.map_replicate]
  have e32 : ebcdicOfLatin1 32 = 64 := by decide +kernel
  have eT : List.map (fun u : U8 => ebcdicOfLatin1 u.val) [48#u8, 49#u8] = [240, 241] := by
    decide +kernel
  have eS : List.map (fun u : U8 => ebcdicOfLatin1 u.val)
      [83#u8, 121#u8, 115#u8, 116#u8, 101#u8, 109#u8, 32#u8, 32#u8, 32#u8, 32#u8] =
      CardDemo.Cbact04c.systemSrc := by decide +kernel
  have eD : List.map (fun u : U8 => ebcdicOfLatin1 u.val) descPre = CardDemo.Cbact04c.descHead := by
    decide +kernel
  simp only [eT, eS, eD, Model.sp, usz_lit_val]
  simp only [e32]

/-! ## Searches on the field values -/

/-- A keyed REWRITE on the field values is a `set` at the first match of the Rust records. -/
theorem replaceFirst_map {α β : Type _} (f : α → β) (q : β → Bool) (y : α) :
    ∀ (l : List α), l.findIdx (q ∘ f) < l.length →
      Model.replaceFirst q (f y) (l.map f) = (l.set (l.findIdx (q ∘ f)) y).map f
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : q (f a) = true
    · have : (a :: l).findIdx (q ∘ f) = 0 := by simp [List.findIdx_cons, ha]
      rw [this]
      simp [Model.replaceFirst, ha]
    · have e : (a :: l).findIdx (q ∘ f) = l.findIdx (q ∘ f) + 1 := by
        simp [List.findIdx_cons, ha]
      rw [e] at h ⊢
      have ih := replaceFirst_map f q y l (by simp only [List.length_cons] at h; omega)
      simp only [List.map_cons, Model.replaceFirst, ha, Bool.false_eq_true, _root_.ite_false,
        List.set_cons_succ, ih]

/-- A first-match search on the field values is the record at the Rust search's index. -/
theorem find_map_getD {α β : Type _} (f : α → β) (q : β → Bool) (d : β) (l : List α)
    (h : l.findIdx (q ∘ f) < l.length) :
    ((l.map f).find? q).getD d = f (l[l.findIdx (q ∘ f)]) := by
  rw [List.find?_map, List.find?_eq_getElem?_findIdx, List.getElem?_eq_getElem h]
  rfl

theorem aId_vals (r : cbact04c_t.AccountRecord) : Model.aId (AccountRecord.vals r) = r.acct_id.val :=
  rfl

theorem aGrp_vals (r : cbact04c_t.AccountRecord) :
    Model.aGrp (AccountRecord.vals r) = r.acct_group_id.val.map ebc := rfl

theorem aBal_vals (r : cbact04c_t.AccountRecord) :
    Model.aBal (AccountRecord.vals r) = r.acct_curr_bal.val := rfl

theorem xAcct_vals (r : cbact04c_t.CardXrefRecord) :
    Model.xAcct (CardXrefRecord.vals r) = r.xref_acct_id.val := rfl

theorem xCard_vals (r : cbact04c_t.CardXrefRecord) :
    Model.xCard (CardXrefRecord.vals r) = r.xref_card_num.val.map ebc := rfl

theorem dRate_vals (r : cbact04c_t.DisGroupRecord) :
    Model.dRate (DisGroupRecord.vals r) = r.dis_int_rate.val := rfl

theorem tAcct_vals (r : cbact04c_t.TranCatBalRecord) :
    Model.tAcct (TranCatBalRecord.vals r) = r.trancat_acct_id.val := rfl

theorem tType_vals (r : cbact04c_t.TranCatBalRecord) :
    Model.tType (TranCatBalRecord.vals r) = r.trancat_type_cd.val.map ebc := rfl

theorem tCat_vals (r : cbact04c_t.TranCatBalRecord) :
    Model.tCat (TranCatBalRecord.vals r) = r.trancat_cd.val := rfl

theorem tBal_vals (r : cbact04c_t.TranCatBalRecord) :
    Model.tBal (TranCatBalRecord.vals r) = r.tran_cat_bal.val := rfl

theorem acctKey_comp (id : Int) :
    ((fun a => Model.aId a == id) ∘ AccountRecord.vals) = (fun r : cbact04c_t.AccountRecord =>
      r.acct_id.val == id) := rfl

theorem xrefKey_comp (id : Int) :
    ((fun x => Model.xAcct x == id) ∘ CardXrefRecord.vals) = (fun r : cbact04c_t.CardXrefRecord =>
      r.xref_acct_id.val == id) := rfl

theorem discKey_comp (group : Std.Array U8 10#usize) (typ : Std.Array U8 2#usize) (cat : I64) :
    ((fun d => Model.dGrp d == group.val.map ebc && Model.dType d == typ.val.map ebc &&
      Model.dCat d == cat.val) ∘ DisGroupRecord.vals) = discKey group typ cat := by
  funext r
  simp only [Function.comp_apply, discKey, Model.dGrp, Model.dType, Model.dCat, DisGroupRecord.vals,
    Model.strOf, Model.numOf, List.getD_cons_succ, List.getD_cons_zero]
  have e1 : (List.map ebc r.dis_acct_group_id.val == List.map ebc group.val) =
      decide (r.dis_acct_group_id.val = group.val) := by
    rw [Bool.eq_iff_iff, beq_iff_eq]; simp only [decide_eq_true_eq]; exact map_ebc_inj
  have e2 : (List.map ebc r.dis_tran_type_cd.val == List.map ebc typ.val) =
      decide (r.dis_tran_type_cd.val = typ.val) := by
    rw [Bool.eq_iff_iff, beq_iff_eq]; simp only [decide_eq_true_eq]; exact map_ebc_inj
  rw [← e1, ← e2]

/-! ## The model's invariant -/

/-- The model's state between two records: the account table differs from the input table only in
the fields a rewrite changes (the ids and groups are kept), and the current account and
cross-reference are the lookups of the last account id, which is in the table. -/
structure MInv (accts0 xrefs : List (List FVal)) (s : Model.St) : Prop where
  ids : s.accts.map (fun a => (Model.aId a, Model.aGrp a)) =
    accts0.map (fun a => (Model.aId a, Model.aGrp a))
  cur : ∀ id, s.lastId = some id → s.acct = Model.findAcct s.accts id ∧
    s.xref = Model.findXref xrefs id ∧ ∃ a ∈ s.accts, Model.aId a = id

theorem minv_init (accts0 xrefs : List (List FVal)) : MInv accts0 xrefs (Model.init accts0) :=
  ⟨rfl, fun id h => by simp [Model.init] at h⟩

theorem replaceFirst_map_same {α β : Type _} (q : α → Bool) (x : α) (g : α → β) :
    ∀ l : List α, (∀ y, l.find? q = some y → g y = g x) →
      (Model.replaceFirst q x l).map g = l.map g
  | [], _ => rfl
  | a :: l, h => by
    by_cases ha : q a = true
    · have := h a (by simp [ha])
      simp [Model.replaceFirst, ha, this]
    · have ih := replaceFirst_map_same q x g l (fun y hy => h y (by simp [ha, hy]))
      simp only [Model.replaceFirst, ha, Bool.false_eq_true, _root_.ite_false, List.map_cons, ih]

theorem posted_aId (a : List FVal) (t : Int) : Model.aId (Model.posted a t) = Model.aId a := by
  simp only [Model.aId, Model.posted, List.getD_eq_getElem?_getD, List.getElem?_set]
  simp

theorem posted_aGrp (a : List FVal) (t : Int) : Model.aGrp (Model.posted a t) = Model.aGrp a := by
  simp only [Model.aGrp, Model.posted, List.getD_eq_getElem?_getD, List.getElem?_set]
  simp

/-- A found account has the id searched for, and is in the table. -/
theorem findAcct_spec (l : List (List FVal)) (id : Int) (h : ∃ a ∈ l, Model.aId a = id) :
    Model.findAcct l id ∈ l ∧ Model.aId (Model.findAcct l id) = id := by
  obtain ⟨a, ha, he⟩ := h
  have hs : (l.find? (fun a => Model.aId a == id)).isSome := by
    rw [List.find?_isSome]; exact ⟨a, ha, by simp [he]⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
  simp only [Model.findAcct, hb, Option.getD_some]
  exact ⟨List.mem_of_find?_eq_some hb, by simpa using List.find?_some hb⟩

/-- Tables with the same ids and groups give lookups with the same group. -/
theorem findAcct_grp (l1 l2 : List (List FVal)) (id : Int)
    (h : l1.map (fun a => (Model.aId a, Model.aGrp a)) = l2.map (fun a => (Model.aId a, Model.aGrp a))) :
    Model.aGrp (Model.findAcct l1 id) = Model.aGrp (Model.findAcct l2 id) := by
  have key : ∀ l : List (List FVal), (l.find? (fun a => Model.aId a == id)).map
      (fun a => (Model.aId a, Model.aGrp a)) =
      (l.map (fun a => (Model.aId a, Model.aGrp a))).find? (fun p => p.1 == id) := by
    intro l; rw [List.find?_map]; rfl
  have e := key l1
  rw [h, ← key l2] at e
  simp only [Model.findAcct]
  cases h1 : l1.find? (fun a => Model.aId a == id) <;>
    cases h2 : l2.find? (fun a => Model.aId a == id) <;> simp_all

theorem step_accts (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal) :
    (Model.step xr dv p c s t).accts =
      if s.lastId = some (Model.tAcct t) then s.accts
      else if s.lastId.isSome then
        Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct) (Model.posted s.acct s.total) s.accts
      else s.accts := by
  dsimp only [Model.step]
  split_ifs <;> rfl

theorem step_lastId (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal) :
    (Model.step xr dv p c s t).lastId = some (Model.tAcct t) := by
  dsimp only [Model.step]
  split_ifs <;> simp_all

theorem step_acct (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal) :
    (Model.step xr dv p c s t).acct =
      if s.lastId = some (Model.tAcct t) then s.acct
      else Model.findAcct (Model.step xr dv p c s t).accts (Model.tAcct t) := by
  rw [step_accts]
  dsimp only [Model.step]
  split_ifs <;> rfl

theorem step_xref (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal) :
    (Model.step xr dv p c s t).xref =
      if s.lastId = some (Model.tAcct t) then s.xref else Model.findXref xr (Model.tAcct t) := by
  dsimp only [Model.step]
  split_ifs <;> rfl

theorem minv_step (accts0 xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (hs : MInv accts0 xr s) (hd : ∃ a ∈ accts0, Model.aId a = Model.tAcct t) :
    MInv accts0 xr (Model.step xr dv p c s t) := by
  have hids : (Model.step xr dv p c s t).accts.map (fun a => (Model.aId a, Model.aGrp a)) =
      accts0.map (fun a => (Model.aId a, Model.aGrp a)) := by
    rw [step_accts]
    split_ifs with h1 h2
    · exact hs.ids
    · obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 h2
      obtain ⟨ha, -, hex⟩ := hs.cur id hid
      obtain ⟨hmem, haid⟩ := findAcct_spec _ _ hex
      rw [replaceFirst_map_same, hs.ids]
      intro y hy
      have hf : s.accts.find? (fun a => Model.aId a == id) = some y := by
        rw [← haid, ← ha]; exact hy
      have : Model.findAcct s.accts id = y := by simp [Model.findAcct, hf]
      rw [posted_aId, posted_aGrp, ha, this]
    · exact hs.ids
  refine ⟨hids, fun id hid => ?_⟩
  rw [step_lastId] at hid
  cases hid
  have hex : ∃ a ∈ (Model.step xr dv p c s t).accts, Model.aId a = Model.tAcct t := by
    obtain ⟨a, ha, he⟩ := hd
    have : (Model.aId a, Model.aGrp a) ∈
        (Model.step xr dv p c s t).accts.map (fun a => (Model.aId a, Model.aGrp a)) := by
      rw [hids]; exact List.mem_map_of_mem ha
    obtain ⟨b, hb, hbe⟩ := List.mem_map.1 this
    exact ⟨b, hb, by simp only [Prod.mk.injEq] at hbe; rw [hbe.1, he]⟩
  refine ⟨?_, ?_, hex⟩
  · rw [step_acct]
    split_ifs with h1
    · obtain ⟨ha, -, -⟩ := hs.cur _ h1
      rw [ha]
      dsimp only [Model.step]
      simp only [h1, _root_.ite_true]
      split_ifs <;> rfl
    · rfl
  · rw [step_xref]
    split_ifs with h1
    · exact (hs.cur _ h1).2.1
    · rfl

end EquivLean.Modernize.Cbact04c.Rust
