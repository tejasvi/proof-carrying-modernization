import EquivLean.Modernize.Cbact04c.Glue
import EquivLean.Modernize.Cbact04c.Domain

/-!
# CBACT04C: coblean's accounts from the input files, and the COBOL outputs

coblean's `cbact04c_events` takes the input as accounts (`Acc`: the account record, its card
cross-reference, its category balances) together with the files' keyed lookups. This file builds
them from the field values of the statement:
- `accsOf` groups the category records by consecutive account id;
- `accOf` gives each group its account record and cross-reference (first match).

The file then proves coblean's hypotheses:
- the accounts are valid (`accsOf_valid`);
- their ids are distinct, because TCATBAL is a KSDS whose key starts with the account id
  (`ksds_tcat`, `groups_distinct`; the only order fact needed is that `bytesLt` is a strict order
  and keys compare by their leading part);
- the keyed READs find the translations' records (`accsOf_acct`, `accsOf_xref`, `accsOf_disc`,
  from `Domain`);
- the clock has two digits of hundredths (`clock_ok`, from `CurrentDate`);
- the harness storage holds `PARM-DATE` and spaces where the transaction records' tails come
  from (`mem_facts`).

`cobol_outputs` combines this with `Glue.run_events`: the COBOL run ends with GOBACK, and its
displays, written transactions and rewritten accounts are `Model.run`'s.
-/

open Cobol EquivLean.Cobol.Rec EquivLean.Modernize.Cbact04c.Model
open CardDemo.Cbact04c (Acc Cat)

namespace EquivLean.Modernize.Cbact04c.Glue

/-! ## VSAM key order -/

theorem bytesLt_irrefl : ∀ a : List UInt8, Sem.bytesLt a a = false
  | [] => rfl
  | x :: xs => by simp [Sem.bytesLt, bytesLt_irrefl xs]

theorem bytesLt_asymm : ∀ a b : List UInt8, Sem.bytesLt a b = true → Sem.bytesLt b a = false
  | [], [], h => by simp [Sem.bytesLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [Sem.bytesLt] at h
  | x :: xs, y :: ys, h => by
    simp only [Sem.bytesLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
    rcases h with h | ⟨rfl, h⟩
    · have : ¬ y < x := by
        intro h'; exact absurd (UInt8.lt_trans h h') (UInt8.lt_irrefl x)
      have : ¬ (y = x) := by rintro rfl; exact UInt8.lt_irrefl y h
      simp_all
    · simp [UInt8.lt_irrefl, bytesLt_asymm xs ys h]

/-- A key compares by its leading part first. -/
theorem bytesLt_prefix : ∀ (p q x y : List UInt8), p.length = q.length →
    Sem.bytesLt (p ++ x) (q ++ y) = true → p = q ∨ Sem.bytesLt p q = true
  | [], [], _, _, _, _ => .inl rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | a :: p, b :: q, x, y, hl, h => by
    simp only [List.cons_append, Sem.bytesLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    rcases h with h | ⟨rfl, h⟩
    · right; simp [Sem.bytesLt, h]
    · rcases bytesLt_prefix p q x y (by simpa using hl) h with h | h
      · left; rw [h]
      · right; simp [Sem.bytesLt, h]

/-- Lexicographic `≤` of byte strings. -/
def LexLe (a b : List UInt8) : Prop := a = b ∨ Sem.bytesLt a b = true

theorem LexLe.antisymm {a b : List UInt8} (h1 : LexLe a b) (h2 : LexLe b a) : a = b := by
  rcases h1 with h1 | h1
  · exact h1
  rcases h2 with h2 | h2
  · exact h2.symm
  · rw [bytesLt_asymm a b h1] at h2; cases h2

/-- The leading part of a category record's key: its account id. -/
def pfx (t : List FVal) : List UInt8 := encodeNum {} CardDemo.Cbact04c.TRANCAT_ACCT_ID.fmt (tAcct t)

theorem tcat_key {t : List FVal} (ht : TranCatBalRecord.Valid t) :
    Sem.keyOf { off := 0, len := 17 } (TranCatBalRecord.encode t) =
      pfx t ++ (tType t ++ encodeNum {} CardDemo.Cbact04c.TRANCAT_CD.fmt (tCat t)) := by
  obtain ⟨he, hc, -, -⟩ := catVals_catOf ht
  have h1 : (encodeNum {} CardDemo.Cbact04c.TRANCAT_ACCT_ID.fmt (tAcct t)).length = 11 :=
    length_encodeNum _ _ _ (by decide)
  have h2 : (encodeNum {} CardDemo.Cbact04c.TRANCAT_CD.fmt (tCat t)).length = 4 :=
    length_encodeNum _ _ _ (by decide)
  have hty : (tType t).length = 2 := hc.1
  have henc := catVals_encode (tAcct t) (catOf t)
  rw [← he] at henc
  rw [henc]
  have hty' : (catOf t).ty.length = 2 := hty
  simp only [Sem.keyOf, List.drop_zero, Cat.bytes, List.append_assoc, catOf, pfx]
  rw [List.take_append, h1, List.take_of_length_le (by omega), List.take_append, hty,
    List.take_of_length_le (by omega), List.take_append, h2, List.take_of_length_le (by omega)]
  simp

theorem pfx_length (t : List FVal) : (pfx t).length = 11 := length_encodeNum _ _ _ (by decide)

/-- **The category records are in account order**: TCATBAL is a KSDS whose key starts with the
account id. -/
theorem ksds_tcat {vals1 : List (List FVal)} (hv : ∀ t ∈ vals1, TranCatBalRecord.Valid t)
    (hk : KsdsValid CardDemo.Cbact04c 1 (vals1.map TranCatBalRecord.encode)) :
    vals1.Pairwise (fun t t' => LexLe (pfx t) (pfx t')) := by
  have e1 : (Sem.fileDecl CardDemo.Cbact04c 1).map (·.org) = some .indexed := by decide
  have e2 : (Sem.fileDecl CardDemo.Cbact04c 1).map (·.key) =
      some (some { off := 0, len := 17 }) := by decide
  unfold KsdsValid at hk
  split at hk
  · rename_i d hd
    rw [hd] at e1 e2
    simp only [Option.map_some, Option.some.injEq] at e1 e2
    have := (hk e1).1 _ e2
    rw [List.pairwise_map] at this
    refine List.Pairwise.imp_of_mem ?_ this
    intro t t' ht ht' h
    rw [tcat_key (hv t ht), tcat_key (hv t' ht')] at h
    exact bytesLt_prefix _ _ _ _ (by rw [pfx_length, pfx_length]) h
  · rename_i hd
    rw [hd] at e1; cases e1

/-! ## The accounts of the input -/

/-- The category records, grouped by consecutive account id (in file order). -/
def groups : List (List FVal) → List (Int × List (List FVal))
  | [] => []
  | t :: ts =>
    match groups ts with
    | [] => [(tAcct t, [t])]
    | (id, g) :: rest =>
      if tAcct t = id then (id, t :: g) :: rest else (tAcct t, [t]) :: (id, g) :: rest

theorem groups_flatten : ∀ ts : List (List FVal), (groups ts).flatMap Prod.snd = ts
  | [] => rfl
  | t :: ts => by
    have ih := groups_flatten ts
    unfold groups
    split
    · rename_i h; rw [h] at ih; simp at ih; simp [ih]
    · rename_i id g rest h
      rw [h] at ih
      split <;> simp_all

theorem groups_ok : ∀ ts : List (List FVal), ∀ g ∈ groups ts, g.2 ≠ [] ∧ ∀ t ∈ g.2, tAcct t = g.1
  | [] => by simp [groups]
  | t :: ts => by
    have ih := groups_ok ts
    unfold groups
    split
    · simp
    · rename_i id g rest h
      rw [h] at ih
      split
      · rename_i hid
        intro g' hg'
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · refine ⟨by simp, fun t' ht' => ?_⟩
          simp only [List.mem_cons] at ht'
          rcases ht' with rfl | ht'
          · exact hid
          · exact (ih (id, g) (by simp)).2 t' ht'
        · exact ih g' (by simp [hg'])
      · intro g' hg'
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | rfl | hg'
        · simp
        · exact ih _ (by simp)
        · exact ih g' (by simp [hg'])

theorem pfx_inj {t t' : List FVal} (ht : TranCatBalRecord.Valid t) (ht' : TranCatBalRecord.Valid t')
    (h : pfx t = pfx t') : tAcct t = tAcct t' := by
  obtain ⟨-, -, hb, h0⟩ := catVals_catOf ht
  obtain ⟨-, -, hb', h0'⟩ := catVals_catOf ht'
  have hh : CardDemo.Cbact04c.TRANCAT_ACCT_ID.fmt.Holds {} (tAcct t) :=
    (holds_display rfl).2 ⟨hb, fun _ => h0⟩
  have hh' : CardDemo.Cbact04c.TRANCAT_ACCT_ID.fmt.Holds {} (tAcct t') :=
    (holds_display rfl).2 ⟨hb', fun _ => h0'⟩
  have := encodeNum_beq (f := CardDemo.Cbact04c.TRANCAT_ACCT_ID.fmt) (by decide) (by decide) hh hh'
  simp only [pfx] at h
  rw [h, beq_self_eq_true] at this
  exact (beq_iff_eq.1 this.symm)

/-- **Distinct accounts**: in account order, the groups have distinct ids. -/
theorem groups_distinct : ∀ ts : List (List FVal), (∀ t ∈ ts, TranCatBalRecord.Valid t) →
    ts.Pairwise (fun t t' => LexLe (pfx t) (pfx t')) →
    (groups ts).Pairwise (fun g h => g.1 ≠ h.1)
  | [], _, _ => by simp [groups]
  | t :: ts, hv, hp => by
    have ih := groups_distinct ts (fun t' h => hv t' (by simp [h])) (List.pairwise_cons.1 hp).2
    have hfl := groups_flatten ts
    have hok := groups_ok ts
    unfold groups
    split
    · simp
    · rename_i id g rest h
      rw [h] at ih hfl hok
      have ihc := List.pairwise_cons.1 ih
      split
      · rename_i hid
        refine List.pairwise_cons.2 ⟨fun g' hg' => ihc.1 g' hg', ihc.2⟩
      · rename_i hid
        refine List.pairwise_cons.2 ⟨fun g' hg' => ?_, ih⟩
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact hid
        · intro he
          -- a record `r` of the later group `g'` has the account of `t`; a record `s` of `g`
          -- lies between them
          obtain ⟨hne', hall'⟩ := hok g' (by simp [hg'])
          obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne'
          obtain ⟨hne, hall⟩ := hok (id, g) (by simp)
          obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hne
          have hsr : LexLe (pfx s) (pfx r) := by
            have hp2 := (List.pairwise_cons.1 hp).2
            rw [← hfl] at hp2
            simp only [List.flatMap_cons] at hp2
            rw [List.pairwise_append] at hp2
            exact hp2.2.2 s hs r (by simp only [List.mem_flatMap]; exact ⟨g', hg', hr⟩)
          have hts : LexLe (pfx t) (pfx s) := (List.pairwise_cons.1 hp).1 s (by
            rw [← hfl]; simp only [List.flatMap_cons, List.mem_append]; exact .inl hs)
          have hrt : pfx r = pfx t := by
            simp only [pfx]; rw [hall' r hr, ← he]
          rw [hrt] at hsr
          have hst := LexLe.antisymm hsr hts
          have hmem_s : s ∈ t :: ts := by
            simp only [List.mem_cons]; right; rw [← hfl]
            simp only [List.flatMap_cons, List.mem_append]; exact .inl hs
          have := pfx_inj (hv s hmem_s) (hv t (by simp)) hst
          rw [hall s hs] at this
          exact hid this.symm

/-- The accounts of the input: one per group of category records. -/
def accsOf (tcat xrefs accts : List (List FVal)) : List Acc :=
  (groups tcat).map fun g => accOf xrefs accts g.1 (g.2.map catOf)

theorem items_accsOf {tcat xrefs accts : List (List FVal)}
    (hv : ∀ t ∈ tcat, TranCatBalRecord.Valid t) :
    (CardDemo.Cbact04c.items (accsOf tcat xrefs accts)).map (fun p => catVals p.1.id p.2) = tcat := by
  have hok := groups_ok tcat
  refine Eq.trans ?_ (groups_flatten tcat)
  simp only [CardDemo.Cbact04c.items, accsOf, List.flatMap_map, List.map_flatMap]
  apply flatMap_congr_mem
  intro g hg
  have hc : (accOf xrefs accts g.1 (g.2.map catOf)).cats = g.2.map catOf := rfl
  have hi : (accOf xrefs accts g.1 (g.2.map catOf)).id = g.1 := rfl
  rw [hc, List.map_map, List.map_map]
  refine Eq.trans ?_ (List.map_id g.2)
  apply List.map_congr_left
  intro t ht
  have htv : TranCatBalRecord.Valid t := hv t (by
    rw [← groups_flatten tcat]; simp only [List.mem_flatMap]; exact ⟨g, hg, ht⟩)
  simp only [Function.comp_apply, id, hi]
  rw [← (hok g hg).2 t ht]
  exact (catVals_catOf htv).1.symm

theorem length_items_accsOf {tcat xrefs accts : List (List FVal)}
    (hv : ∀ t ∈ tcat, TranCatBalRecord.Valid t) :
    (CardDemo.Cbact04c.items (accsOf tcat xrefs accts)).length = tcat.length := by
  have := congrArg List.length (items_accsOf (xrefs := xrefs) (accts := accts) hv)
  simpa using this

theorem accsOf_distinct {tcat xrefs accts : List (List FVal)}
    (hv : ∀ t ∈ tcat, TranCatBalRecord.Valid t)
    (hk : KsdsValid CardDemo.Cbact04c 1 (tcat.map TranCatBalRecord.encode)) :
    (accsOf tcat xrefs accts).Pairwise (fun a b => a.id ≠ b.id) := by
  have := groups_distinct tcat hv (ksds_tcat hv hk)
  simp only [accsOf, List.pairwise_map]
  exact this

theorem xref_shape {X : List FVal} (hX : CardXrefRecord.Valid X) :
    ∃ card cust acct fill, X = [.str card, .num cust, .num acct, .str fill] ∧ card.length = 16 ∧
      cust.natAbs < 1000000000 ∧ 0 ≤ cust ∧ acct.natAbs < 100000000000 ∧ 0 ≤ acct ∧
      fill.length = 14 := by
  have hl : X.length = 4 := hX.length_eq.symm
  match X, hl, hX with
  | [x0, x1, x2, x3], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))) =>
    obtain ⟨card, rfl, hc⟩ := str_of_valid rfl h0
    obtain ⟨cust, rfl, hcu⟩ := num_of_valid rfl h1
    obtain ⟨acct, rfl, hac⟩ := num_of_valid rfl h2
    obtain ⟨fill, rfl, hf⟩ := str_of_valid rfl h3
    obtain ⟨_, k1, -, -, n1, -⟩ := hcu
    obtain ⟨_, k2, -, -, n2, -⟩ := hac
    cases k1; cases k2
    rw [holds_display rfl] at n1 n2
    exact ⟨card, cust, acct, fill, rfl, hc, n1.1, n1.2 rfl, n2.1, n2.2 rfl, hf⟩

theorem disc_shape {D : List FVal} (hD : DisGroupRecord.Valid D) :
    ∃ grp ty cat rate fill, D = [.str grp, .str ty, .num cat, .num rate, .str fill] ∧
      grp.length = 10 ∧ ty.length = 2 ∧ cat.natAbs < 10000 ∧ 0 ≤ cat ∧
      rate.natAbs < 1000000 ∧ fill.length = 28 := by
  have hl : D.length = 5 := hD.length_eq.symm
  match D, hl, hD with
  | [x0, x1, x2, x3, x4], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 .nil)))) =>
    obtain ⟨grp, rfl, hg⟩ := str_of_valid rfl h0
    obtain ⟨ty, rfl, ht⟩ := str_of_valid rfl h1
    obtain ⟨cat, rfl, hca⟩ := num_of_valid rfl h2
    obtain ⟨rate, rfl, hr⟩ := num_of_valid rfl h3
    obtain ⟨fill, rfl, hf⟩ := str_of_valid rfl h4
    obtain ⟨_, k2, -, -, n2, -⟩ := hca
    obtain ⟨_, k3, -, -, n3, -⟩ := hr
    cases k2; cases k3
    rw [holds_display rfl] at n2 n3
    exact ⟨grp, ty, cat, rate, fill, rfl, hg, ht, n2.1, n2.2 rfl, n3.1, hf⟩

/-- A first-match search for an element that exists finds an element with the property. -/
theorem find?_of_exists {α : Type} {l : List α} {p : α → Bool} (h : ∃ x ∈ l, p x = true) :
    ∃ x, l.find? p = some x ∧ x ∈ l ∧ p x = true := by
  have : (l.find? p).isSome := List.find?_isSome.2 h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 this
  exact ⟨x, hx, List.mem_of_find?_eq_some hx, List.find?_some hx⟩

theorem findAcct_found {accts : List (List FVal)} {id : Int} (h : ∃ a ∈ accts, aId a = id) :
    findAcct accts id ∈ accts ∧ aId (findAcct accts id) = id := by
  obtain ⟨x, hx, hm, hp⟩ := find?_of_exists (p := fun a => aId a == id)
    (by obtain ⟨a, ha, he⟩ := h; exact ⟨a, ha, by simp [he]⟩)
  simp only [findAcct, hx, Option.getD_some]
  exact ⟨hm, by simpa using hp⟩

theorem findXref_found {xrefs : List (List FVal)} {id : Int} (h : ∃ x ∈ xrefs, xAcct x = id) :
    findXref xrefs id ∈ xrefs ∧ xAcct (findXref xrefs id) = id := by
  obtain ⟨x, hx, hm, hp⟩ := find?_of_exists (p := fun x => xAcct x == id)
    (by obtain ⟨a, ha, he⟩ := h; exact ⟨a, ha, by simp [he]⟩)
  simp only [findXref, hx, Option.getD_some]
  exact ⟨hm, by simpa using hp⟩

/-- **Every account of the input is `AccOk`**, in the domain. -/
theorem accsOf_ok {tcat xrefs accts discs : List (List FVal)} {link : List FVal}
    (hv1 : ∀ t ∈ tcat, TranCatBalRecord.Valid t) (hv2 : ∀ x ∈ xrefs, CardXrefRecord.Valid x)
    (hv3 : ∀ a ∈ accts, AccountRecord.Valid a) (hD : Domain tcat xrefs accts discs link) :
    ∀ a ∈ accsOf tcat xrefs accts, AccOk xrefs accts a := by
  intro a ha
  simp only [accsOf, List.mem_map] at ha
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨hne, hall⟩ := groups_ok tcat g hg
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
  have htm : t ∈ tcat := by
    rw [← groups_flatten tcat]; simp only [List.mem_flatMap]; exact ⟨g, hg, ht⟩
  have hid : tAcct t = g.1 := hall t ht
  obtain ⟨hA, hX, -⟩ := hD.2 t htm
  rw [hid] at hA hX
  obtain ⟨hAm, hAid⟩ := findAcct_found hA
  obtain ⟨hXm, -⟩ := findXref_found hX
  obtain ⟨-, -, hb, h0⟩ := catVals_catOf (hv1 t htm)
  rw [hid] at hb h0
  obtain ⟨card, cust, acct, fill, hXe, hcard, -⟩ := xref_shape (hv2 _ hXm)
  refine ⟨rfl, hv3 _ hAm, hAid, hb, h0, ?_, ?_, ?_, ?_⟩
  · intro c hc
    change c ∈ g.2.map catOf at hc
    simp only [List.mem_map] at hc
    obtain ⟨t', ht', rfl⟩ := hc
    have ht'm : t' ∈ tcat := by
      rw [← groups_flatten tcat]; simp only [List.mem_flatMap]; exact ⟨g, hg, ht'⟩
    exact (catVals_catOf (hv1 t' ht'm)).2.1
  · show g.2.map catOf ≠ []
    simpa using hne
  · show (xCard (findXref xrefs g.1)).length = 16
    rw [hXe]; exact hcard
  · show (CardXrefRecord.encode (findXref xrefs g.1)).take 16 = xCard (findXref xrefs g.1)
    rw [hXe]
    have e : CardXrefRecord.encode [.str card, .num cust, .num acct, .str fill] =
        card ++ (encodeNum {} CardDemo.Cbact04c.XREF_CUST_ID.fmt cust ++
          (encodeNum {} CardDemo.Cbact04c.XREF_ACCT_ID.fmt acct ++ (fill ++ []))) := rfl
    rw [e, List.take_left' hcard]
    rfl

/-! ## coblean's lookups find the translations' records -/

theorem findKey_of_find? {α : Type} [Inhabited α] (k : KeyDecl) (v : List UInt8)
    (g : α → List UInt8) (p : α → Bool) (l : List α)
    (hp : ∀ x ∈ l, (Sem.keyOf k (g x) == v) = p x) {x : α} (hx : l.find? p = some x) :
    ∃ i, Sem.findKey k v (l.map g) = some i ∧ (l.map g).getD i [] = g x := by
  have h := findKey_map k v g p l hp
  rw [hx] at h
  cases hf : Sem.findKey k v (l.map g) with
  | none => rw [hf] at h; cases h
  | some i =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hi : i < l.length := by simpa using findKey_lt' hf
    refine ⟨i, rfl, ?_⟩
    rw [← h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl

theorem acct_keyOf {A : List FVal} (hA : AccountRecord.Valid A) :
    Sem.keyOf { off := 0, len := 11 } (AccountRecord.encode A) =
      encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt (aId A) ∧
    CardDemo.Cbact04c.FD_ACCT_ID.fmt.Holds {} (aId A) := by
  obtain ⟨i, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, hi, hi0, -⟩ := acct_shape hA
  have e : AccountRecord.encode [.num i, .str s, .num bal, .num cl, .num ccl, .str od, .str ed,
      .str rd, .num cc, .num cd, .str zip, .str grp, .str af] =
      encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt i ++ (s ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CURR_BAL.fmt bal ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CREDIT_LIMIT.fmt cl ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CASH_CREDIT_LIMIT.fmt ccl ++ (od ++ (ed ++ (rd ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CURR_CYC_CREDIT.fmt cc ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CURR_CYC_DEBIT.fmt cd ++
      (zip ++ (grp ++ (af ++ [])))))))))))) := rfl
  have hl : (encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt i).length = 11 :=
    length_encodeNum _ _ _ (by decide)
  refine ⟨?_, (holds_display rfl).2 ⟨hi, fun _ => hi0⟩⟩
  rw [e]
  simp only [Sem.keyOf, List.drop_zero, aId, numOf, List.getD_cons_zero]
  exact List.take_left' hl

theorem xref_keyOf {X : List FVal} (hX : CardXrefRecord.Valid X) :
    Sem.keyOf { off := 25, len := 11 } (CardXrefRecord.encode X) =
      encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt (xAcct X) ∧
    CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt.Holds {} (xAcct X) := by
  obtain ⟨card, cust, acct, fill, rfl, hc, -, -, ha, ha0, -⟩ := xref_shape hX
  have e : CardXrefRecord.encode [.str card, .num cust, .num acct, .str fill] =
      (card ++ encodeNum {} CardDemo.Cbact04c.XREF_CUST_ID.fmt cust) ++
        (encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt acct ++ (fill ++ [])) := by
    show card ++ (_ ++ (_ ++ (fill ++ []))) = _
    simp only [List.append_assoc]; rfl
  have h1 : (card ++ encodeNum {} CardDemo.Cbact04c.XREF_CUST_ID.fmt cust).length = 25 := by
    rw [List.length_append, hc, length_encodeNum _ _ _ (by decide)]; rfl
  have hl : (encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt acct).length = 11 :=
    length_encodeNum _ _ _ (by decide)
  refine ⟨?_, (holds_display rfl).2 ⟨ha, fun _ => ha0⟩⟩
  rw [e]
  simp only [Sem.keyOf, xAcct, numOf]
  rw [List.drop_left' h1, List.take_left' hl]
  rfl

theorem disc_encode {D : List FVal} (hD : DisGroupRecord.Valid D) :
    DisGroupRecord.encode D = dGrp D ++ dType D ++
      encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt (dCat D) ++
      encodeNum {} CardDemo.Cbact04c.DIS_INT_RATE.fmt (dRate D) ++ strOf (D.getD 4 default) := by
  obtain ⟨grp, ty, cat, rate, fill, rfl, -⟩ := disc_shape hD
  show grp ++ (ty ++ (_ ++ (_ ++ (fill ++ [])))) = _
  simp [dGrp, dType, dCat, dRate, strOf, numOf, List.append_assoc]
  rfl

theorem disc_keyOf {D : List FVal} (hD : DisGroupRecord.Valid D) :
    Sem.keyOf { off := 0, len := 16 } (DisGroupRecord.encode D) =
      dGrp D ++ dType D ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt (dCat D) := by
  obtain ⟨grp, ty, cat, rate, fill, hDe, hg, ht, -⟩ := disc_shape hD
  have h4 : (encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt (dCat D)).length = 4 :=
    length_encodeNum _ _ _ (by decide)
  have hgl : (dGrp D).length = 10 := by rw [hDe]; exact hg
  have htl : (dType D).length = 2 := by rw [hDe]; exact ht
  rw [disc_encode hD]
  have e : dGrp D ++ dType D ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt (dCat D) ++
      encodeNum {} CardDemo.Cbact04c.DIS_INT_RATE.fmt (dRate D) ++ strOf (D.getD 4 default) =
      (dGrp D ++ dType D ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt (dCat D)) ++
      (encodeNum {} CardDemo.Cbact04c.DIS_INT_RATE.fmt (dRate D) ++ strOf (D.getD 4 default)) := by
    simp only [List.append_assoc]
  rw [e]
  simp only [Sem.keyOf, List.drop_zero]
  exact List.take_left' (by simp only [List.length_append, hgl, htl, h4])

/-- The disclosure key comparison is field by field. -/
theorem disc_key_beq {g g' t t' : List UInt8} {c c' : Int} (hg : g.length = 10)
    (hg' : g'.length = 10) (ht : t.length = 2) (ht' : t'.length = 2)
    (hc : CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt.Holds {} c)
    (hc' : CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt.Holds {} c') :
    (g ++ t ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c ==
      g' ++ t' ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c') =
      (g == g' && t == t' && c == c') := by
  have he := encodeNum_beq (f := CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt) (by decide) (by decide) hc hc'
  have h4 : ∀ v, (encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt v).length = 4 :=
    fun v => length_encodeNum _ _ _ (by decide)
  by_cases h1 : g = g'
  · subst h1
    by_cases h2 : t = t'
    · subst h2
      by_cases h3 : c = c'
      · subst h3; simp
      · have : (encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c ==
            encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c') = false := by
          rw [he]; simpa using h3
        simp only [List.append_assoc, beq_self_eq_true, Bool.true_and]
        rw [show (c == c') = false by simpa using h3]
        simpa using this
    · have : (g ++ t ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c ==
          g ++ t' ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c') = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, List.append_assoc, List.append_cancel_left_eq]
        intro h
        exact h2 (List.append_inj h (by rw [ht, ht'])).1
      rw [this]; simp [h2]
  · have : (g ++ t ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c ==
        g' ++ t' ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c') = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, List.append_assoc]
      intro h
      exact h1 (List.append_inj h (by rw [hg, hg'])).1
    rw [this]; simp [h1]

/-! ## The harness storage, the linkage record, the clock -/

cobol_mem_hex initMem from "init_mem.hex"

set_option maxRecDepth 10000 in
theorem initMem_size : initMem.size = 1739 := by rfl

theorem link_shape {link : List FVal} (hl : ExternalParms.Valid link) :
    ∃ len date, link = [.num len, .str date] ∧ date.length = 10 ∧
      (ExternalParms.encode link).length = 12 := by
  have hlen : link.length = 2 := hl.length_eq.symm
  match link, hlen, hl with
  | [x0, x1], _, .cons h0 (.cons h1 .nil) =>
    obtain ⟨len, rfl, hlv⟩ := num_of_valid rfl h0
    obtain ⟨date, rfl, hd⟩ := str_of_valid rfl h1
    refine ⟨len, date, rfl, hd, ?_⟩
    have e : ExternalParms.encode [.num len, .str date] =
        (encodeNum {} CardDemo.Cbact04c.PARM_LENGTH.fmt len) ++ (date ++ []) := rfl
    have h2 : (encodeNum {} CardDemo.Cbact04c.PARM_LENGTH.fmt len).length = 2 :=
      length_encodeNum _ _ _ (by decide)
    rw [e, List.length_append, h2]; simp [hd]

/-- The storage the COBOL run starts from: the harness storage with the linkage record. -/
theorem mem_facts {link : List FVal} (hl : ExternalParms.Valid link) :
    (Mem.write initMem 1727 (ExternalParms.encode link)).size = 1739 ∧
    (Mem.write initMem 1727 (ExternalParms.encode link)).read 1729 10 = parmOf link ∧
    (Mem.write initMem 1727 (ExternalParms.encode link)).read 1314 76 = sp 76 ∧
    (Mem.write initMem 1727 (ExternalParms.encode link)).read 1588 20 = sp 20 := by
  obtain ⟨len, date, rfl, hd, he⟩ := link_shape hl
  have h76 : initMem.read 1314 76 = sp 76 := by decide +kernel
  have h20 : initMem.read 1588 20 = sp 20 := by decide +kernel
  refine ⟨by rw [Mem.size_write, initMem_size], ?_, ?_, ?_⟩
  · rw [Mem.read_write_within _ _ _ _ _ (by omega) (by rw [he]; decide)
      (by rw [he, initMem_size]; decide)]
    have e : ExternalParms.encode [.num len, .str date] =
        (encodeNum {} CardDemo.Cbact04c.PARM_LENGTH.fmt len) ++ (date ++ []) := rfl
    have h2 : (encodeNum {} CardDemo.Cbact04c.PARM_LENGTH.fmt len).length = 2 :=
      length_encodeNum _ _ _ (by decide)
    rw [e, List.drop_left' h2]
    simp [parmOf, strOf, List.take_of_length_le, hd]
  · rw [Mem.read_write_disjoint _ _ _ _ _ (by omega), h76]
  · rw [Mem.read_write_disjoint _ _ _ _ _ (by omega), h20]

theorem enc2 : ∀ d1, d1 < 10 → ∀ d2, d2 < 10 →
    encodeNum {} { digits := 2 } ((10 * d1 + d2 : Nat) : Int) =
      [UInt8.ofNat (240 + d1), UInt8.ofNat (240 + d2)] := by decide

theorem byte_digit {b : UInt8} (h1 : 240 ≤ b) (h2 : b ≤ 249) :
    ∃ d, d < 10 ∧ b = UInt8.ofNat (240 + d) := by
  rw [UInt8.le_iff_toNat_le] at h1 h2
  simp only [UInt8.toNat_ofNat] at h1 h2
  refine ⟨b.toNat - 240, by omega, ?_⟩
  apply UInt8.toNat_inj.1
  have hs : UInt8.size = 256 := rfl
  rw [UInt8.toNat_ofNat_of_lt' (by omega)]
  omega

/-- A `CURRENT-DATE` reading has two digits of hundredths at 14. -/
theorem clock_ok {clk : List UInt8} (hc : CurrentDate clk) :
    ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧ 0 ≤ mil ∧
      clk = pre ++ encodeNum {} { digits := 2 } mil ++ post := by
  obtain ⟨hl, hd, -⟩ := hc
  obtain ⟨h14a, h14b⟩ := hd 14 (by decide) (by decide)
  obtain ⟨h15a, h15b⟩ := hd 15 (by decide) (by decide)
  obtain ⟨d1, hd1, e1⟩ := byte_digit h14a h14b
  obtain ⟨d2, hd2, e2⟩ := byte_digit h15a h15b
  refine ⟨clk.take 14, ((10 * d1 + d2 : Nat) : Int), clk.drop 16, by simp [hl], by simp [hl],
    by simp; omega, by omega, ?_⟩
  rw [enc2 d1 hd1 d2 hd2, ← e1, ← e2]
  match clk, hl with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

/-! ## coblean's hypotheses for the accounts of the input -/

theorem accsOf_mem {tcat xrefs accts : List (List FVal)} {a : Acc}
    (ha : a ∈ accsOf tcat xrefs accts) :
    ∃ g ∈ groups tcat, a = accOf xrefs accts g.1 (g.2.map catOf) ∧ g.2 ≠ [] ∧
      (∀ t ∈ g.2, t ∈ tcat ∧ tAcct t = g.1) := by
  simp only [accsOf, List.mem_map] at ha
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨hne, hall⟩ := groups_ok tcat g hg
  refine ⟨g, hg, rfl, hne, fun t ht => ⟨?_, hall t ht⟩⟩
  rw [← groups_flatten tcat]; simp only [List.mem_flatMap]; exact ⟨g, hg, ht⟩

theorem find?_getD_of_exists {l : List (List FVal)} {p : List FVal → Bool}
    (h : ∃ x ∈ l, p x = true) : l.find? p = some ((l.find? p).getD []) := by
  obtain ⟨x, hx, -, -⟩ := find?_of_exists h
  rw [hx]; rfl

/-- **The accounts of the input are valid accounts of coblean's model.** -/
theorem accsOf_valid {tcat xrefs accts discs : List (List FVal)} {link : List FVal}
    (hv1 : ∀ t ∈ tcat, TranCatBalRecord.Valid t) (hv2 : ∀ x ∈ xrefs, CardXrefRecord.Valid x)
    (hv3 : ∀ a ∈ accts, AccountRecord.Valid a) (hD : Domain tcat xrefs accts discs link) :
    ∀ a ∈ accsOf tcat xrefs accts, a.valid := by
  intro a ha
  have hok := accsOf_ok hv1 hv2 hv3 hD a ha
  obtain ⟨g, -, rfl, hne, hall⟩ := accsOf_mem ha
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨htm, hid⟩ := hall t ht
  obtain ⟨-, hX, -⟩ := hD.2 t htm
  rw [hid] at hX
  obtain ⟨hXm, -⟩ := findXref_found hX
  have hxl := Schema.length_encode (s := CardXrefRecord) (by decide) (hv2 _ hXm)
  have hvalA : AccountRecord.Valid (findAcct accts g.1) := hok.valid
  obtain ⟨i, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, hA, hi, hi0, hs, hbal, hcl, hccl,
    hod, hed, hrd, hcc, hcd, hzip, hgrp, haf⟩ := acct_shape hvalA
  have e12 : ∀ v, (encodeNum {} CardDemo.Cbact04c.ACCT_CREDIT_LIMIT.fmt v).length = 12 :=
    fun v => length_encodeNum _ _ _ (by decide)
  have e12' : ∀ v, (encodeNum {} CardDemo.Cbact04c.ACCT_CASH_CREDIT_LIMIT.fmt v).length = 12 :=
    fun v => length_encodeNum _ _ _ (by decide)
  refine ⟨hok.idb, hok.id0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hok.ne, hok.cats⟩ <;>
    simp only [accOf, hA, aBal, aGrp, strOf, numOf, List.getD_cons_zero, List.getD_cons_succ] <;>
    simp_all [List.length_append]

/-- The lookups of every account of the input succeed (`Domain`). -/
theorem accsOf_found {tcat xrefs accts discs : List (List FVal)} {link : List FVal}
    (hD : Domain tcat xrefs accts discs link) : ∀ a ∈ accsOf tcat xrefs accts,
      (∃ A ∈ accts, aId A = a.id) ∧ (∃ X ∈ xrefs, xAcct X = a.id) ∧
      ∀ c ∈ a.cats, ∃ d ∈ discs, dGrp d = aGrp (findAcct accts a.id) ∧ dType d = c.ty ∧
        dCat d = c.cat := by
  intro a ha
  obtain ⟨g, -, rfl, hne, hall⟩ := accsOf_mem ha
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨htm, hid⟩ := hall t ht
  obtain ⟨hA, hX, -⟩ := hD.2 t htm
  refine ⟨hid ▸ hA, hid ▸ hX, fun c hc => ?_⟩
  change c ∈ g.2.map catOf at hc
  simp only [List.mem_map] at hc
  obtain ⟨t', ht', rfl⟩ := hc
  obtain ⟨ht'm, hid'⟩ := hall t' ht'
  obtain ⟨-, -, hdisc⟩ := hD.2 t' ht'm
  rw [hid'] at hdisc
  exact hdisc

/-- coblean's keyed READ of the account file finds the account's record. -/
theorem accsOf_acct {tcat xrefs accts discs : List (List FVal)} {link : List FVal}
    (hv1 : ∀ t ∈ tcat, TranCatBalRecord.Valid t) (hv2 : ∀ x ∈ xrefs, CardXrefRecord.Valid x)
    (hv3 : ∀ a ∈ accts, AccountRecord.Valid a) (hD : Domain tcat xrefs accts discs link) :
    ∀ a ∈ accsOf tcat xrefs accts, ∃ i,
      Sem.findKey { off := 0, len := 11 } (encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt a.id)
        (accts.map AccountRecord.encode) = some i ∧
      (accts.map AccountRecord.encode).getD i [] = a.bytes := by
  intro a ha
  have hok := accsOf_ok hv1 hv2 hv3 hD a ha
  obtain ⟨⟨A, hAm, hAid⟩, -, -⟩ := accsOf_found hD a ha
  have hh : CardDemo.Cbact04c.FD_ACCT_ID.fmt.Holds {} a.id :=
    (holds_display rfl).2 ⟨hok.idb, fun _ => hok.id0⟩
  have hx := find?_getD_of_exists (l := accts) (p := fun A => aId A == a.id)
    ⟨A, hAm, by simp [hAid]⟩
  obtain ⟨i, hi, hg⟩ := findKey_of_find? { off := 0, len := 11 }
    (encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt a.id) AccountRecord.encode
    (fun A => aId A == a.id) accts (fun A hA => by
      obtain ⟨e, hA'⟩ := acct_keyOf (hv3 A hA)
      rw [e]; exact encodeNum_beq (by decide) (by decide) hA' hh) hx
  have hb := accOf_bytes xrefs accts a.id a.cats hok.valid hok.found
  rw [← hok.eq] at hb
  exact ⟨i, hi, by rw [hg, hb]; rfl⟩

/-- coblean's keyed READ of the cross-reference file (alternate key) finds the account's. -/
theorem accsOf_xref {tcat xrefs accts discs : List (List FVal)} {link : List FVal}
    (hv1 : ∀ t ∈ tcat, TranCatBalRecord.Valid t) (hv2 : ∀ x ∈ xrefs, CardXrefRecord.Valid x)
    (hv3 : ∀ a ∈ accts, AccountRecord.Valid a) (hD : Domain tcat xrefs accts discs link) :
    ∀ a ∈ accsOf tcat xrefs accts, ∃ i,
      Sem.findKey { off := 25, len := 11 }
        (encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt a.id)
        (xrefs.map CardXrefRecord.encode) = some i ∧
      (xrefs.map CardXrefRecord.encode).getD i [] = a.xrec := by
  intro a ha
  have hok := accsOf_ok hv1 hv2 hv3 hD a ha
  obtain ⟨-, ⟨X, hXm, hXid⟩, -⟩ := accsOf_found hD a ha
  have hh : CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt.Holds {} a.id :=
    (holds_display rfl).2 ⟨hok.idb, fun _ => hok.id0⟩
  have hx := find?_getD_of_exists (l := xrefs) (p := fun X => xAcct X == a.id)
    ⟨X, hXm, by simp [hXid]⟩
  obtain ⟨i, hi, hg⟩ := findKey_of_find? { off := 25, len := 11 }
    (encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt a.id) CardXrefRecord.encode
    (fun X => xAcct X == a.id) xrefs (fun X hX => by
      obtain ⟨e, hX'⟩ := xref_keyOf (hv2 X hX)
      rw [e]; exact encodeNum_beq (by decide) (by decide) hX' hh) hx
  refine ⟨i, hi, ?_⟩
  rw [hg, hok.eq]
  rfl

/-- The `FILLER` of the disclosure group record of account `a` and category `c`. -/
def dfillOf (discs : List (List FVal)) (a : Acc) (c : Cat) : List UInt8 :=
  strOf (((discs.find? (fun d => dGrp d == a.grp && dType d == c.ty && dCat d == c.cat)).getD
    []).getD 4 default)

/-- coblean's keyed READ of the disclosure group file finds the rate the translations use. -/
theorem accsOf_disc {tcat xrefs accts discs : List (List FVal)} {link : List FVal}
    (hv1 : ∀ t ∈ tcat, TranCatBalRecord.Valid t) (hv2 : ∀ x ∈ xrefs, CardXrefRecord.Valid x)
    (hv3 : ∀ a ∈ accts, AccountRecord.Valid a) (hv4 : ∀ d ∈ discs, DisGroupRecord.Valid d)
    (hD : Domain tcat xrefs accts discs link) :
    ∀ a ∈ accsOf tcat xrefs accts, ∀ c ∈ a.cats, ∃ i,
      Sem.findKey { off := 0, len := 16 }
        (a.grp ++ c.ty ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c.cat)
        (discs.map DisGroupRecord.encode) = some i ∧
      (discs.map DisGroupRecord.encode).getD i [] =
        a.grp ++ c.ty ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c.cat ++
          encodeNum {} CardDemo.Cbact04c.DIS_INT_RATE.fmt (rateOf discs a c) ++ dfillOf discs a c ∧
      (dfillOf discs a c).length = 28 ∧ (rateOf discs a c).natAbs < 1000000 := by
  intro a ha c hc
  have hok := accsOf_ok hv1 hv2 hv3 hD a ha
  have hav := accsOf_valid hv1 hv2 hv3 hD a ha
  obtain ⟨-, -, hdisc⟩ := accsOf_found hD a ha
  obtain ⟨d, hdm, hdg, hdt, hdc⟩ := hdisc c hc
  have hgrp : a.grp = aGrp (findAcct accts a.id) := by rw [hok.eq]; rfl
  obtain ⟨hcty, -, hccat, hccat0, -⟩ := hok.cats c hc
  have hgl : a.grp.length = 10 := hav.2.2.2.2.2.2.2.2.1
  let p : List FVal → Bool := fun d => dGrp d == a.grp && dType d == c.ty && dCat d == c.cat
  obtain ⟨D0, hx, hD0m, hpD0⟩ := find?_of_exists (l := discs) (p := p)
    ⟨d, hdm, by simp [p, hdg, hdt, hdc, hgrp]⟩
  have hcH : CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt.Holds {} c.cat :=
    (holds_display rfl).2 ⟨hccat, fun _ => hccat0⟩
  obtain ⟨i, hi, hg⟩ := findKey_of_find? { off := 0, len := 16 }
    (a.grp ++ c.ty ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c.cat)
    DisGroupRecord.encode p discs (fun D hDm => by
      obtain ⟨grp, ty, cat, rate, fill, hDe, hg, ht, hcat, hcat0, -⟩ := disc_shape (hv4 D hDm)
      rw [disc_keyOf (hv4 D hDm)]
      have hDg : (dGrp D).length = 10 := by rw [hDe]; exact hg
      have hDt : (dType D).length = 2 := by rw [hDe]; exact ht
      have hDc : CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt.Holds {} (dCat D) := by
        rw [hDe]; exact (holds_display rfl).2 ⟨hcat, fun _ => hcat0⟩
      exact disc_key_beq hDg hgl hDt hcty hDc hcH) hx
  obtain ⟨grp0, ty0, cat0, rate0, fill0, hD0e, -, -, -, -, hr0, hf0⟩ := disc_shape (hv4 D0 hD0m)
  have hp0 : dGrp D0 = a.grp ∧ dType D0 = c.ty ∧ dCat D0 = c.cat := by
    have h := hpD0
    simp only [p, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hrate : rateOf discs a c = dRate D0 := by
    simp only [rateOf, findRate]
    show dRate ((discs.find? p).getD []) = dRate D0
    rw [hx]; rfl
  have hfill : dfillOf discs a c = strOf (D0.getD 4 default) := by
    simp only [dfillOf]
    show strOf (((discs.find? p).getD []).getD 4 default) = _
    rw [hx]; rfl
  refine ⟨i, hi, ?_, ?_, ?_⟩
  · rw [hg, disc_encode (hv4 D0 hD0m), hp0.1, hp0.2.1, hp0.2.2, hrate, hfill]
  · rw [hfill, hD0e]; exact hf0
  · rw [hrate, hD0e]; exact hr0

theorem startMsg_text : CardDemo.Cbact04c.startMsg.map cp037Code =
    txt "START OF EXECUTION OF PROGRAM CBACT04C" := by decide +kernel
theorem endMsg_text : CardDemo.Cbact04c.endMsg.map cp037Code =
    txt "END OF EXECUTION OF PROGRAM CBACT04C" := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- **CBACT04C's COBOL run outputs what `Model.run` says**, for every input of the statement's
domain: KSDS category records, valid field values, a `CURRENT-DATE` clock reading, the linkage
record in the harness storage. -/
theorem cobol_outputs (vals1 vals2 vals3 vals4 : List (List FVal)) (link1 : List FVal)
    (clk : List UInt8)
    (hv1 : ∀ v ∈ vals1, TranCatBalRecord.Valid v) (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, AccountRecord.Valid v) (hv4 : ∀ v ∈ vals4, DisGroupRecord.Valid v)
    (hl : ExternalParms.Valid link1) (hc : CurrentDate clk)
    (hk1 : KsdsValid CardDemo.Cbact04c 1 (vals1.map TranCatBalRecord.encode))
    (hD : Domain vals1 vals2 vals3 vals4 link1) (n : Nat) (hn : vals1.length < n) :
    let r := CardDemo.Cbact04c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
          (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])
    let o := Model.run vals1 vals2 vals3 vals4 (parmOf link1) clk
    r.1 = .stop .goback ∧ (displays r.2).map (·.map cp037Code) = o.disp ∧
      (writes 5 r.2).map TranRecord.decode = o.writes.map some ∧
      (rewrites 3 r.2).map AccountRecord.decode = o.rewrites.map some := by
  intro r o
  simp only [r, o]
  have hok := accsOf_ok (xrefs := vals2) (accts := vals3) hv1 hv2 hv3 hD
  have hval := accsOf_valid (xrefs := vals2) (accts := vals3) hv1 hv2 hv3 hD
  have hdist := accsOf_distinct (xrefs := vals2) (accts := vals3) hv1 hk1
  have hitems := items_accsOf (xrefs := vals2) (accts := vals3) hv1
  have hlen := length_items_accsOf (xrefs := vals2) (accts := vals3) hv1
  have hacct := accsOf_acct hv1 hv2 hv3 hD
  have hxref := accsOf_xref hv1 hv2 hv3 hD
  have hdisc := accsOf_disc hv1 hv2 hv3 hv4 hD
  obtain ⟨hm, hparm, hdesc, hfill⟩ := mem_facts hl
  have hclk : ∀ k : Nat, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ (fun _ => clk) k = pre ++ encodeNum {} { digits := 2 } mil ++ post :=
    fun _ => clock_ok hc
  have hfile1 : vals1.map TranCatBalRecord.encode =
      (CardDemo.Cbact04c.items (accsOf vals1 vals2 vals3)).map (fun p => Cat.bytes p.1.id p.2) := by
    conv => lhs; rw [← hitems]
    rw [List.map_map]
    exact List.map_congr_left fun p _ => catVals_encode _ _
  -- coblean's theorem, for the accounts of the input
  have hev := CardDemo.Cbact04c.cbact04c_events (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
    hm (fun _ => clk) hclk (accsOf vals1 vals2 vals3) hval hdist (by rw [hlen]; exact hD.1)
    (vals3.map AccountRecord.encode) (vals2.map CardXrefRecord.encode)
    (vals4.map DisGroupRecord.encode)
    (fun a => (Sem.findKey { off := 0, len := 11 }
      (encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt a.id) (vals3.map AccountRecord.encode)).getD 0)
    (fun a => (Sem.findKey { off := 25, len := 11 }
      (encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt a.id)
        (vals2.map CardXrefRecord.encode)).getD 0)
    (fun a ha => by
      obtain ⟨i, hi, hg⟩ := hacct a ha
      rw [hi]; exact ⟨rfl, hg⟩)
    (fun a ha => by
      obtain ⟨i, hi, hg⟩ := hxref a ha
      rw [hi]; exact ⟨rfl, hg⟩)
    (rateOf vals4)
    (fun a c => (Sem.findKey { off := 0, len := 16 }
      (a.grp ++ c.ty ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c.cat)
        (vals4.map DisGroupRecord.encode)).getD 0)
    (dfillOf vals4)
    (fun a ha c hc => by
      obtain ⟨i, hi, hg, hf, hr⟩ := hdisc a ha c hc
      rw [hi]; exact ⟨rfl, hg, hf, hr⟩)
    n (by rw [hlen]; exact hn)
  simp only [hparm, hdesc, hfill] at hev
  rw [← hfile1] at hev
  obtain ⟨hstop, hout⟩ := hev
  -- the translations' model, for the same accounts
  obtain ⟨hd, hw, hrw⟩ := run_events (xrefs := vals2) (accts := vals3) (discs := vals4)
    (parm := parmOf link1) (clk := clk) (by obtain ⟨_, _, rfl, hd, _⟩ := link_shape hl; exact hd)
    (by rw [hc.1]; decide) (accsOf vals1 vals2 vals3) hok hdist (by rw [hlen]; exact hD.1)
  rw [hitems] at hd hw hrw
  refine ⟨hstop, ?_, ?_, ?_⟩
  · rw [hd]
    simp only [displays, hout, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.filterMap_append, List.map_append]
    simp [dispOf, startMsg_text, endMsg_text]
    rfl
  · rw [hw]
    simp only [writes, hout, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.filterMap_append, List.map_append]
    simp [wrOf]
    rfl
  · rw [hrw]
    simp only [rewrites, hout, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.filterMap_append, List.map_append]
    simp [rwOf]
    rfl

end EquivLean.Modernize.Cbact04c.Glue
