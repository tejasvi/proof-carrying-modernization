import EquivLean.Modernize.Cbstm03a.Domain
import EquivLean.Modernize.Cbstm03a.Java.JRunHL
import EquivLean.Modernize.Cbstm03a.JavaStatement

/-!
# CBSTM03A → Java: the statement's domain gives the load records' domain

`domainT_of_facts`: for valid transaction records sorted by card (`CardsSorted`) in at most 50 groups (`grp`) of
at most 10, the facts the statement's domain `Domain` states of them, the load records the Java reads from their
texts (`recOf (trnxTextR (trnxROfD v)) 350`) are in `DomainT`.

* the card of a load record is the CP037 text of the record's card bytes (`card_rec`, `card_valid`);
* `groupsOf` (built from the right) and `grp` (built from the left) are both the run-length encoding of the cards
  (`groupsOf_eq_rle`, `grp_map`), and the encoding commutes with the one-to-one CP037 text (`rle_map`);
* CP037 keeps the byte order: `ebc` of the text of byte `b` is `b` (`ebcIdx_cp037`), so the EBCDIC comparison of
  two texts is the byte comparison of their bytes (`ebcScan_cp037`); sorted cards with distinct consecutive runs
  are strictly increasing (`ebcAsc_rle`).
-/

open Cobol EquivLean.Cobol.Rec
open Cobol.StmCore (grp)
open Jimple (JStr I64)
open EquivLean.Modernize.Cbstm03b.Java (fixStr fixStr_length fixStr_eq_self fixStr_eq_take cp037Str_inj cp037Unit_inj
  cp037Str_length)
open EquivLean.Modernize.Cbstm03a.StmBridge (strOf numOf)

namespace EquivLean.Modernize.Cbstm03a.Java.Dom

/-! ## The record objects of the field values (equiv-lean's `trnxROf`, verbatim) -/

def jStrOfD (v : List EquivLean.Cobol.Rec.FVal) (i : Nat) : JStr := cp037Str (strOf (v.getD i default))
def i64OfD (v : List EquivLean.Cobol.Rec.FVal) (i : Nat) : I64 := BitVec.ofInt 64 (numOf (v.getD i default))
def trnxROfD (v : List EquivLean.Cobol.Rec.FVal) : TrnxR :=
  ⟨jStrOfD v 0, jStrOfD v 1, jStrOfD v 2, i64OfD v 3, jStrOfD v 4, jStrOfD v 5, i64OfD v 6,
   i64OfD v 7, jStrOfD v 8, jStrOfD v 9, jStrOfD v 10, jStrOfD v 11, jStrOfD v 12, jStrOfD v 13⟩

/-! ## The card of a load record -/

theorem take_fixStr (s : JStr) : ∀ {k n : Nat}, k ≤ n → (fixStr s n).take k = fixStr s k
  | k, 0, h => by rw [Nat.le_zero.mp h]; rfl
  | k, n + 1, h => by
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · simp only [fixStr]
      rw [List.take_append_of_le_length (by rw [fixStr_length]; omega), take_fixStr s (by omega)]
    · rw [show k = n + 1 by omega]
      exact List.take_of_length_le (by rw [fixStr_length])

/-- The card of the load record of `v`: the card field's text, cut or padded to 16 characters. -/
theorem card_rec (v : List EquivLean.Cobol.Rec.FVal) :
    sub (recOf (trnxTextR (trnxROfD v)) 350) 0 16 = fixStr (jStrOfD v 0) 16 := by
  simp only [sub, recOf, List.drop_zero, List.take_take]
  rw [show min 16 350 = 16 from rfl, take_fixStr _ (by omega), fixStr_eq_take ?_]
  · simp only [trnxTextR, trnxROfD, List.append_assoc]
    exact List.take_left' (fixStr_length _ _)
  · simp only [trnxTextR, List.length_append, fixStr_length]
    omega

/-- A valid record of a schema whose first field is a 16-byte alphanumeric field starts with that field's
bytes. -/
theorem first_field {s : Schema} {f : Field} {fs : List Field} (hs : s.fields = f :: fs)
    (hk : ∃ j, f.desc.kind = .alnum j) (hl : f.desc.len = 16) {v : List EquivLean.Cobol.Rec.FVal}
    (hv : s.Valid v) :
    ∃ bs rest, v = .str bs :: rest ∧ bs.length = 16 ∧ StmCore.tCard (s.encode v) = bs := by
  unfold Schema.Valid at hv
  rw [hs] at hv
  rcases v with _ | ⟨a, rest⟩
  · cases hv
  · have h0 : f.Valid a := by cases hv; assumption
    cases a with
    | num x =>
      obtain ⟨fmt, hk', -⟩ := h0
      obtain ⟨j, hj⟩ := hk
      rw [hj] at hk'
      cases hk'
    | str bs =>
      have hb : bs.length = 16 := h0.2.trans hl
      refine ⟨bs, rest, rfl, hb, ?_⟩
      simp only [Schema.encode, hs, List.zip_cons_cons, List.flatMap_cons, Field.encode, StmCore.tCard]
      exact List.take_left' hb

/-- The card of the load record of a valid `v`: the CP037 text of the record's card (16 bytes). -/
theorem card_valid {v : List EquivLean.Cobol.Rec.FVal} (hv : TrnxRecord.Valid v) :
    fixStr (jStrOfD v 0) 16 = cp037Str (StmCore.tCard (TrnxRecord.encode v)) ∧
      (StmCore.tCard (TrnxRecord.encode v)).length = 16 := by
  obtain ⟨bs, rest, rfl, hb, ht⟩ := first_field (s := TrnxRecord) rfl ⟨_, rfl⟩ rfl hv
  rw [ht]
  refine ⟨?_, hb⟩
  simp only [jStrOfD, List.getD_cons_zero, strOf]
  exact fixStr_eq_self (by rw [cp037Str_length]; exact hb)

/-! ## Run-length encoding -/

/-- One element more in front of a run-length encoding. -/
def rleCons {α : Type} [DecidableEq α] (b : α) : List (α × Nat) → List (α × Nat)
  | (c, n) :: gs => if b = c then (c, n + 1) :: gs else (b, 1) :: (c, n) :: gs
  | [] => [(b, 1)]

/-- The runs of equal consecutive elements, each with its length (built from the right, as `groupsOf`). -/
def rle {α : Type} [DecidableEq α] : List α → List (α × Nat)
  | [] => []
  | a :: xs => rleCons a (rle xs)

/-- One element more at the end of a run-length encoding (as `grpSnoc`). -/
def rleSnoc {α : Type} [DecidableEq α] (R : List (α × Nat)) (a : α) : List (α × Nat) :=
  match R.getLast? with
  | some p => if p.1 = a then R.dropLast ++ [(p.1, p.2 + 1)] else R ++ [(a, 1)]
  | none => [(a, 1)]

theorem rleSnoc_cons_cons {α : Type} [DecidableEq α] (p q : α × Nat) (gs : List (α × Nat)) (a : α) :
    rleSnoc (p :: q :: gs) a = p :: rleSnoc (q :: gs) a := by
  unfold rleSnoc
  rw [List.getLast?_cons_cons]
  rcases h : (q :: gs).getLast? with _ | r
  · simp at h
  · simp only [List.dropLast_cons_cons, List.cons_append]
    by_cases hr : r.1 = a <;> simp [hr]

theorem rleCons_rleSnoc {α : Type} [DecidableEq α] (b a : α) :
    ∀ R : List (α × Nat), rleCons b (rleSnoc R a) = rleSnoc (rleCons b R) a
  | [] => by
    by_cases h : b = a
    · subst h; simp [rleCons, rleSnoc]
    · simp [rleCons, rleSnoc, h]
  | [(c, n)] => by
    by_cases h1 : c = a
    · subst h1
      by_cases h2 : b = c
      · subst h2; simp [rleCons, rleSnoc]
      · simp [rleCons, rleSnoc, h2]
    · by_cases h2 : b = c
      · subst h2; simp [rleCons, rleSnoc, h1]
      · simp [rleCons, rleSnoc, h1, h2]
  | (c, n) :: q :: gs => by
    rw [rleSnoc_cons_cons]
    by_cases h : b = c
    · simp [rleCons, h, rleSnoc_cons_cons]
    · simp [rleCons, h, rleSnoc_cons_cons]

theorem rle_snoc {α : Type} [DecidableEq α] (a : α) : ∀ l : List α, rle (l ++ [a]) = rleSnoc (rle l) a
  | [] => by simp [rle, rleCons, rleSnoc]
  | b :: l => by
    show rleCons b (rle (l ++ [a])) = rleSnoc (rleCons b (rle l)) a
    rw [rle_snoc a l, rleCons_rleSnoc]

/-- The first run is the first element's. -/
theorem rle_cons_head {α : Type} [DecidableEq α] (a : α) (xs : List α) : ∃ n gs, rle (a :: xs) = (a, n) :: gs := by
  show ∃ n gs, rleCons a (rle xs) = (a, n) :: gs
  generalize rle xs = R
  rcases R with _ | ⟨⟨c, m⟩, gs⟩
  · exact ⟨1, [], rfl⟩
  · by_cases h : a = c
    · subst h; exact ⟨m + 1, gs, by simp [rleCons]⟩
    · exact ⟨1, (c, m) :: gs, by simp [rleCons, h]⟩

theorem rle_head_mem {α : Type} [DecidableEq α] {l : List α} {c : α} {n : Nat} {gs : List (α × Nat)}
    (h : rle l = (c, n) :: gs) : c ∈ l := by
  rcases l with _ | ⟨d, ds⟩
  · cases h
  · obtain ⟨n', gs', h'⟩ := rle_cons_head d ds
    rw [h'] at h
    cases h
    exact List.mem_cons_self

/-- The encoding commutes with a one-to-one map. -/
theorem rle_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ l : List α, rle (l.map f) = (rle l).map (fun p => (f p.1, p.2))
  | [] => rfl
  | a :: xs => by
    show rleCons (f a) (rle (xs.map f)) = (rleCons a (rle xs)).map _
    rw [rle_map f hf xs]
    generalize rle xs = R
    rcases R with _ | ⟨⟨c, n⟩, gs⟩
    · rfl
    · by_cases h : a = c
      · subst h; simp [rleCons]
      · have h' : f a ≠ f c := fun e => h (hf _ _ e)
        simp [rleCons, h, h']

/-! ## `groupsOf` and `grp` as run-length encodings of the cards -/

theorem groupsOf_eq_rle : ∀ rs : List JStr, groupsOf rs = rle (rs.map (fun r => sub r 0 16))
  | [] => rfl
  | r :: rs => by
    rw [List.map_cons]
    show _ = rleCons (sub r 0 16) (rle (rs.map (fun r => sub r 0 16)))
    rw [← groupsOf_eq_rle rs]
    simp only [groupsOf]
    generalize groupsOf rs = G
    rcases G with _ | ⟨⟨c, n⟩, gs⟩ <;> rfl

/-- A group's card and size. -/
def gKey (g : List (List UInt8)) : List UInt8 × Nat := (StmCore.gCard g, g.length)

theorem gCard_single (r : List UInt8) : StmCore.gCard [r] = StmCore.tCard r := rfl

theorem gCard_snoc (g : List (List UInt8)) (r : List UInt8) : StmCore.gCard (g ++ [r]) = StmCore.tCard r := by
  simp [StmCore.gCard]

theorem grpSnoc_map (gs : List (List (List UInt8))) (r : List UInt8) :
    (StmCore.grpSnoc gs r).map gKey = rleSnoc (gs.map gKey) (StmCore.tCard r) := by
  unfold StmCore.grpSnoc rleSnoc
  rw [List.getLast?_map]
  rcases h : gs.getLast? with _ | g
  · rfl
  · by_cases hc : StmCore.gCard g = StmCore.tCard r
    · simp [hc, gKey, gCard_snoc]
    · simp [hc, gKey, gCard_single]

theorem grp_map (rs : List (List UInt8)) : (StmCore.grp rs).map gKey = rle (rs.map StmCore.tCard) := by
  induction rs using StmCore.list_snoc_ind with
  | nil => rfl
  | snoc rs r ih =>
    rw [StmCore.grp_snoc, grpSnoc_map, ih, List.map_append, List.map_cons, List.map_nil, rle_snoc]

/-! ## CP037 keeps the byte order -/

set_option maxRecDepth 100000 in
theorem ebcIdx_cp037_fin : ∀ b : Fin 256, ebcIdx (cp037Unit (UInt8.ofNat b.val)).toNat = b.val := by
  decide +kernel

/-- `ebc` of the text of byte `b` is `b`. -/
theorem ebcIdx_cp037 (b : UInt8) : ebcIdx (cp037Unit b).toNat = b.toNat := by
  have h := ebcIdx_cp037_fin ⟨b.toNat, b.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  exact h

/-- The sign of a comparison. -/
def ordSign : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1

theorem cmpBytes_self : ∀ a : List UInt8, Sem.cmpBytes a a = .eq
  | [] => Sem.cmpBytes.eq_2 _ _ (fun _ _ _ _ h _ => by cases h)
  | x :: xs => by
    rw [Sem.cmpBytes.eq_1, ite_eq_right (UInt8.lt_irrefl x), ite_eq_right (UInt8.lt_irrefl x), cmpBytes_self xs]

theorem cmpBytes_eq : ∀ {a b : List UInt8}, a.length = b.length → Sem.cmpBytes a b = .eq → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: a, y :: b, hl, h => by
    rw [Sem.cmpBytes.eq_1] at h
    by_cases h1 : x < y
    · rw [ite_eq_left h1] at h; cases h
    · by_cases h2 : y < x
      · rw [ite_eq_right h1, ite_eq_left h2] at h; cases h
      · rw [ite_eq_right h1, ite_eq_right h2] at h
        have h1' := mt UInt8.lt_iff_toNat_lt.mpr h1
        have h2' := mt UInt8.lt_iff_toNat_lt.mpr h2
        have hxy : x = y := UInt8.toNat_inj.mp (by omega)
        rw [hxy, cmpBytes_eq (by simpa using hl) h]

/-- The EBCDIC scan of two CP037 texts is the byte comparison of their bytes. -/
theorem ebcScan_cp037 : ∀ a b : List UInt8, ebcScan (cp037Str a) (cp037Str b) = ordSign (Sem.cmpBytes a b)
  | [], b => by
    show ebcScan [] (cp037Str b) = ordSign (Sem.cmpBytes [] b)
    rw [ebcScan.eq_2 _ _ (fun _ _ _ _ h _ => by cases h), Sem.cmpBytes.eq_2 _ _ (fun _ _ _ _ h _ => by cases h)]
    rfl
  | x :: a, [] => by
    show ebcScan (cp037Str (x :: a)) [] = ordSign (Sem.cmpBytes (x :: a) [])
    rw [ebcScan.eq_2 _ _ (fun _ _ _ _ _ h => by cases h), Sem.cmpBytes.eq_2 _ _ (fun _ _ _ _ _ h => by cases h)]
    rfl
  | x :: a, y :: b => by
    show ebcScan (cp037Unit x :: cp037Str a) (cp037Unit y :: cp037Str b) = ordSign (Sem.cmpBytes (x :: a) (y :: b))
    rw [ebcScan.eq_1, Sem.cmpBytes.eq_1, ebcIdx_cp037, ebcIdx_cp037]
    by_cases h1 : x < y
    · have hne : cp037Unit x ≠ cp037Unit y := fun e => by
        have := cp037Unit_inj e; subst this; exact UInt8.lt_irrefl _ h1
      have h1' : x.toNat < y.toNat := UInt8.lt_iff_toNat_lt.mp h1
      rw [ite_eq_left ⟨hne, by omega⟩, ite_eq_left h1', ite_eq_left h1]
      rfl
    · by_cases h2 : y < x
      · have hne : cp037Unit x ≠ cp037Unit y := fun e => by
          have := cp037Unit_inj e; subst this; exact UInt8.lt_irrefl _ h2
        have h2' : y.toNat < x.toNat := UInt8.lt_iff_toNat_lt.mp h2
        rw [ite_eq_left ⟨hne, by omega⟩, ite_eq_right (by omega), ite_eq_right h1, ite_eq_left h2]
        rfl
      · have h1' := mt UInt8.lt_iff_toNat_lt.mpr h1
        have h2' := mt UInt8.lt_iff_toNat_lt.mpr h2
        have hxy : x = y := UInt8.toNat_inj.mp (by omega)
        subst hxy
        rw [ite_eq_right (fun h => h.1 rfl), ite_eq_right h1, ite_eq_right h1, ebcScan_cp037 a b]

/-- Two 16-byte cards in increasing byte order have CP037 texts in increasing EBCDIC order. -/
theorem ebcCmp_cp037_lt {a b : List UInt8} (ha : a.length = 16) (hb : b.length = 16)
    (h : Sem.cmpBytes a b = .lt) : ebcCmp (cp037Str a) (cp037Str b) < 0 := by
  have hne : cp037Str a ≠ cp037Str b := by
    intro e
    rw [cp037Str_inj e, cmpBytes_self] at h
    cases h
  have hm : max (cp037Str a).length (cp037Str b).length = 16 := by
    rw [cp037Str_length, cp037Str_length, ha, hb]; rfl
  unfold ebcCmp
  rw [ite_eq_right hne, hm, fixStr_eq_self (by rw [cp037Str_length]; exact ha),
    fixStr_eq_self (by rw [cp037Str_length]; exact hb), ebcScan_cp037, h]
  decide

/-- Sorted 16-byte cards: the runs' cards are strictly increasing in EBCDIC order. -/
theorem ebcAsc_rle : ∀ ks : List (List UInt8), ks.Pairwise (fun a b => Sem.cmpBytes a b ≠ .gt) →
    (∀ k ∈ ks, k.length = 16) → EbcAsc ((rle ks).map (fun p => cp037Str p.1))
  | [], _, _ => trivial
  | a :: xs, hp, hl => by
    have ih := ebcAsc_rle xs (List.pairwise_cons.mp hp).2 (fun k hk => hl k (List.mem_cons_of_mem _ hk))
    have hmem : ∀ c n gs, rle xs = (c, n) :: gs → c ∈ xs := fun _ _ _ h => rle_head_mem h
    show EbcAsc ((rleCons a (rle xs)).map _)
    revert ih hmem
    generalize rle xs = R
    intro ih hmem
    rcases R with _ | ⟨⟨c, n⟩, gs⟩
    · exact trivial
    · have hc := hmem c n gs rfl
      by_cases h : a = c
      · subst h
        simpa [rleCons] using ih
      · simp only [rleCons, ite_eq_right h, List.map_cons]
        refine ⟨?_, by simpa using ih⟩
        apply ebcCmp_cp037_lt (hl a List.mem_cons_self) (hl c (List.mem_cons_of_mem _ hc))
        have hgt := (List.pairwise_cons.mp hp).1 c hc
        cases hcmp : Sem.cmpBytes a c with
        | lt => rfl
        | eq => exact absurd (cmpBytes_eq ((hl a List.mem_cons_self).trans
            (hl c (List.mem_cons_of_mem _ hc)).symm) hcmp) h
        | gt => exact absurd hcmp hgt

/-! ## The theorem -/

/-- **The load records are in `DomainT`.** `CardsSorted` is `Domain`'s (the body of `Cobol.StmCore.CardsSorted`). -/
theorem domainT_of_facts (vals1 : List (List EquivLean.Cobol.Rec.FVal)) (hv : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hS : CardsSorted (vals1.map TrnxRecord.encode)) (hG : (grp (vals1.map TrnxRecord.encode)).length ≤ 50)
    (hT : ∀ g ∈ grp (vals1.map TrnxRecord.encode), g.length ≤ 10) :
    DomainT (((vals1.map trnxROfD).map trnxTextR).map (recOf · 350)) := by
  obtain ⟨ks, hks⟩ : ∃ ks, ks = (vals1.map TrnxRecord.encode).map StmCore.tCard := ⟨_, rfl⟩
  have hcards : (((vals1.map trnxROfD).map trnxTextR).map (recOf · 350)).map (fun r => sub r 0 16) =
      ks.map cp037Str := by
    rw [hks]
    simp only [List.map_map]
    apply List.map_congr_left
    intro v hvm
    simp only [Function.comp_apply]
    rw [card_rec, (card_valid (hv v hvm)).1]
  have hlen : ∀ k ∈ ks, k.length = 16 := by
    intro k hk
    rw [hks, List.map_map, List.mem_map] at hk
    obtain ⟨v, hvm, rfl⟩ := hk
    simp only [Function.comp_apply]
    exact (card_valid (hv v hvm)).2
  have hsorted : ks.Pairwise (fun a b => Sem.cmpBytes a b ≠ .gt) := by
    rw [hks, List.pairwise_map]
    exact hS
  have hg : groupsOf (((vals1.map trnxROfD).map trnxTextR).map (recOf · 350)) =
      (rle ks).map (fun p => (cp037Str p.1, p.2)) := by
    rw [groupsOf_eq_rle, hcards, rle_map cp037Str (fun _ _ h => cp037Str_inj h)]
  have hr : rle ks = (grp (vals1.map TrnxRecord.encode)).map gKey := by
    rw [hks, grp_map]
  refine ⟨?_, ?_, ?_⟩
  · rw [hg, List.length_map, hr, List.length_map]
    exact hG
  · intro g hgm
    rw [hg, hr, List.map_map, List.mem_map] at hgm
    obtain ⟨g', hg'm, rfl⟩ := hgm
    exact hT g' hg'm
  · rw [hg, List.map_map]
    exact ebcAsc_rle ks hsorted hlen

end EquivLean.Modernize.Cbstm03a.Java.Dom
