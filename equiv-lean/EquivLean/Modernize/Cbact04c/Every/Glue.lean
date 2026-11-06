import EquivLean.Modernize.Cbact04c.Accs
import EquivLean.Modernize.Cbact04c.ModelEvery
import EquivLean.Modernize.Cbact04c.Every.Domain
import EquivLean.Demo.Cobol.Cbact04c.Every

/-!
# CBACT04C on every input: the translations' model and coblean's `cbact04c_every`

coblean's `cbact04c_every` describes CBACT04C's run on every input as `model4x`, a fold over the
category records paired with their accounts (`items accs`), reading the account,
cross-reference and disclosure group files by key; a failed read abends (999), a missing
disclosure group is retried with group `DEFAULT`.  `Model.runE` is the fold the translations
perform on field values.

`cobol_outputs`: for the statement's inputs, the COBOL run ends with `GOBACK` or abend 999, and
its displayed lines, written transactions, rewritten accounts and abend flag are `Model.runE`'s.
The proof is a simulation, one record at a time (`step_corr`), with the record lemmas of the
direct-hit route (`Cbact04c.Glue`, `Cbact04c.Accs`).  Its invariant is `Corr`:
- the current account was read before any rewrite of it;
- the account table differs from the file only at accounts already left.
-/

open Cobol EquivLean.Cobol.Rec EquivLean.Modernize.Cbact04c.Model
open EquivLean.Modernize.Cbact04c.Glue
open CardDemo.Cbact04c (Acc Cat Disc)

namespace EquivLean.Modernize.Cbact04c.Every.Glue

/-! ## The files as coblean's model reads them -/

/-- An account record as coblean's `Acc` (its cross-reference and categories are not used). -/
def acctAcc (A : List FVal) : Acc := accOf [] [A] (aId A) []

theorem findAcct_single (A : List FVal) : findAcct [A] (aId A) = A := by
  simp [findAcct]

theorem acctAcc_bytes {A : List FVal} (hA : AccountRecord.Valid A) :
    (acctAcc A).bytes = AccountRecord.encode A := by
  have h := accOf_bytes [] [A] (aId A) [] (by rw [findAcct_single]; exact hA)
    (by rw [findAcct_single])
  rwa [findAcct_single] at h

theorem decode_acctAcc_posted {A : List FVal} (hA : AccountRecord.Valid A) (t : Int) :
    AccountRecord.decode ((acctAcc A).posted t) = some (posted A t) := by
  obtain ⟨e, hv⟩ := posted_bytes [] [A] (aId A) [] t (by rw [findAcct_single]; exact hA)
    (by rw [findAcct_single])
  rw [findAcct_single] at e hv
  unfold acctAcc
  rw [e]
  exact Schema.decode_encode (by decide) hv

theorem acctAcc_grp (A : List FVal) : (acctAcc A).grp = aGrp A := by
  simp [acctAcc, accOf, findAcct_single]

theorem acctAcc_validRec {A : List FVal} (hA : AccountRecord.Valid A) : (acctAcc A).validRec := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, hid, hid0, hs, hbal, hcl,
    hccl, hod, hed, hrd, hcc, hcd, hzip, hgrp, haf⟩ := acct_shape hA
  have h1 : (encodeNum {} CardDemo.Cbact04c.ACCT_CREDIT_LIMIT.fmt cl).length = 12 :=
    length_encodeNum _ _ _ (by decide)
  have h2 : (encodeNum {} CardDemo.Cbact04c.ACCT_CASH_CREDIT_LIMIT.fmt ccl).length = 12 :=
    length_encodeNum _ _ _ (by decide)
  refine ⟨hid, hid0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [acctAcc, accOf, findAcct, aId, aBal, aGrp, numOf, strOf, hs, hbal, hcc, hcd, hzip, hgrp,
      haf, hod, hed, hrd, h1, h2]

/-- A disclosure group record as coblean's `Disc`. -/
def discOf (D : List FVal) : Disc :=
  ⟨dGrp D ++ dType D ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt (dCat D), dRate D,
    strOf (D.getD 4 default)⟩

theorem discOf_bytes {D : List FVal} (hD : DisGroupRecord.Valid D) :
    (discOf D).bytes = DisGroupRecord.encode D := by
  rw [disc_encode hD]; rfl

theorem discOf_valid {D : List FVal} (hD : DisGroupRecord.Valid D) : (discOf D).valid := by
  obtain ⟨grp, ty, cat, rate, fill, rfl, hg, ht, -, -, hr, hf⟩ := disc_shape hD
  have h4 : (encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt cat).length = 4 :=
    length_encodeNum _ _ _ (by decide)
  refine ⟨?_, hr, hf⟩
  simp [discOf, dGrp, dType, dCat, strOf, numOf, hg, ht, h4]

theorem xref_take {X : List FVal} (hX : CardXrefRecord.Valid X) :
    (CardXrefRecord.encode X).take 16 = xCard X := by
  obtain ⟨card, cust, acct, fill, rfl, hc, -⟩ := xref_shape hX
  show (card ++ (_ ++ (_ ++ (fill ++ [])))).take 16 = card
  exact List.take_left' hc

/-! ## coblean's lookups are the translations' first-match searches -/

theorem acctIdx_eq {accts : List (List FVal)} (hv : ∀ A ∈ accts, AccountRecord.Valid A) {id : Int}
    (hid : CardDemo.Cbact04c.FD_ACCT_ID.fmt.Holds {} id) :
    (CardDemo.Cbact04c.acctIdx (accts.map acctAcc) id).map
      (fun i => (accts.map acctAcc).getD i CardDemo.Cbact04c.acc0) = (findAcctO accts id).map acctAcc := by
  have hb : (accts.map acctAcc).map Acc.bytes = accts.map AccountRecord.encode := by
    rw [List.map_map]; exact List.map_congr_left (fun A hA => acctAcc_bytes (hv A hA))
  have h := findKey_map { off := 0, len := 11 } (encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt id)
    AccountRecord.encode (fun a => aId a == id) accts (fun A hA => by
      obtain ⟨hk, hh⟩ := acct_keyOf (hv A hA)
      rw [hk]; exact encodeNum_beq (by decide) (by decide) hh hid)
  unfold CardDemo.Cbact04c.acctIdx findAcctO
  rw [hb, ← h]
  cases hf : Sem.findKey { off := 0, len := 11 } (encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt id)
    (accts.map AccountRecord.encode) with
  | none => rfl
  | some i =>
    have hi : i < accts.length := by simpa using findKey_lt' hf
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem xrefIdx_eq {xrefs : List (List FVal)} (hv : ∀ X ∈ xrefs, CardXrefRecord.Valid X) {id : Int}
    (hid : CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt.Holds {} id) :
    (CardDemo.Cbact04c.xrefIdx (xrefs.map CardXrefRecord.encode) id).map
      (fun j => ((xrefs.map CardXrefRecord.encode).getD j []).take 16) =
      (findXrefO xrefs id).map xCard := by
  have h := findKey_map { off := 25, len := 11 }
    (encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt id) CardXrefRecord.encode
    (fun x => xAcct x == id) xrefs (fun X hX => by
      obtain ⟨hk, hh⟩ := xref_keyOf (hv X hX)
      rw [hk]; exact encodeNum_beq (by decide) (by decide) hh hid)
  unfold CardDemo.Cbact04c.xrefIdx findXrefO
  rw [← h]
  cases hf : Sem.findKey { off := 25, len := 11 }
    (encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt id) (xrefs.map CardXrefRecord.encode) with
  | none => rfl
  | some j =>
    have hj : j < xrefs.length := by simpa using findKey_lt' hf
    have hm : xrefs[j] ∈ xrefs := List.getElem_mem hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
      xref_take (hv _ hm)]

theorem discIdx_eq {discs : List (List FVal)} (hv : ∀ D ∈ discs, DisGroupRecord.Valid D)
    {grp : List UInt8} {c : Cat} (hg : grp.length = 10) (hc : c.valid) :
    (CardDemo.Cbact04c.discIdx (discs.map discOf) grp c).map
      (fun i => ((discs.map discOf).getD i CardDemo.Cbact04c.disc0).rate) =
      findRateO discs grp c.ty c.cat := by
  obtain ⟨hty, -, hcat, hcat0, -⟩ := hc
  have hb : (discs.map discOf).map Disc.bytes = discs.map DisGroupRecord.encode := by
    rw [List.map_map]; exact List.map_congr_left (fun D hD => discOf_bytes (hv D hD))
  have hch : CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt.Holds {} c.cat :=
    (holds_display rfl).2 ⟨hcat, fun _ => hcat0⟩
  have h := findKey_map { off := 0, len := 16 }
    (grp ++ c.ty ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c.cat)
    DisGroupRecord.encode (fun d => dGrp d == grp && dType d == c.ty && dCat d == c.cat) discs
    (fun D hD => by
      obtain ⟨g', t', cat', r', f', hDe, hg', ht', hc', hc0', -⟩ := disc_shape (hv D hD)
      rw [disc_keyOf (hv D hD)]
      have hgl : (dGrp D).length = 10 := by rw [hDe]; exact hg'
      have htl : (dType D).length = 2 := by rw [hDe]; exact ht'
      have hdh : CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt.Holds {} (dCat D) := by
        rw [hDe]; exact (holds_display rfl).2 ⟨hc', fun _ => hc0'⟩
      exact disc_key_beq hgl hg htl hty hdh hch)
  unfold CardDemo.Cbact04c.discIdx findRateO
  rw [hb, ← h]
  cases hf : Sem.findKey { off := 0, len := 16 }
    (grp ++ c.ty ++ encodeNum {} CardDemo.Cbact04c.DIS_TRAN_CAT_CD.fmt c.cat)
    (discs.map DisGroupRecord.encode) with
  | none => rfl
  | some i =>
    have hi : i < discs.length := by simpa using findKey_lt' hf
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, discOf]

/-! ## The lines of the error paths -/

set_option maxRecDepth 10000 in
theorem notFound_text : CardDemo.Cbact04c.notFoundMsg.map cp037Code = txt "ACCOUNT NOT FOUND: " := by
  decide +kernel

theorem notFound_acct_text {id : Int} :
    (CardDemo.Cbact04c.notFoundMsg ++ encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt id).map
      cp037Code = txt "ACCOUNT NOT FOUND: " ++ zpad 11 id.natAbs := by
  rw [List.map_append, notFound_text,
    text_unsigned (fmt := CardDemo.Cbact04c.FD_ACCT_ID.fmt) rfl rfl (by decide)]

theorem notFound_xref_text {id : Int} :
    (CardDemo.Cbact04c.notFoundMsg ++ encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt id).map
      cp037Code = txt "ACCOUNT NOT FOUND: " ++ zpad 11 id.natAbs := by
  rw [List.map_append, notFound_text,
    text_unsigned (fmt := CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt) rfl rfl (by decide)]

set_option maxRecDepth 10000 in
theorem errAcct_text : CardDemo.Cbact04c.errAcctMsg.map cp037Code =
    txt "ERROR READING ACCOUNT FILE" := by decide +kernel
set_option maxRecDepth 10000 in
theorem errXref_text : CardDemo.Cbact04c.errXrefMsg.map cp037Code =
    txt "ERROR READING XREF FILE" := by decide +kernel
set_option maxRecDepth 10000 in
theorem missing_text : CardDemo.Cbact04c.missingMsg.map cp037Code =
    txt "DISCLOSURE GROUP RECORD MISSING" := by decide +kernel
set_option maxRecDepth 10000 in
theorem tryDefault_text : CardDemo.Cbact04c.tryDefaultMsg.map cp037Code =
    txt "TRY WITH DEFAULT GROUP CODE" := by decide +kernel
set_option maxRecDepth 10000 in
theorem errDefault_text : CardDemo.Cbact04c.errDefaultMsg.map cp037Code =
    txt "ERROR READING DEFAULT DISCLOSURE GROUP" := by decide +kernel
set_option maxRecDepth 10000 in
theorem status23_text : CardDemo.Cbact04c.status23Msg.map cp037Code =
    txt "FILE STATUS IS: NNNN0023" := by decide +kernel
set_option maxRecDepth 10000 in
theorem abend_text : CardDemo.Cbact04c.abendMsg.map cp037Code = txt "ABENDING PROGRAM" := by
  decide +kernel
theorem defaultGrp_eq : CardDemo.Cbact04c.defaultGrp = defaultGrp := rfl

/-! ## The accounts of the category file -/

/-- Each account's category records together (the statement's `Domain`). -/
def Together (ts : List (List FVal)) : Prop :=
  ∀ i j k, i < j → j < k → k < ts.length →
    tAcct (ts.getD i []) = tAcct (ts.getD k []) → tAcct (ts.getD j []) = tAcct (ts.getD i [])

theorem Together.tail {t : List FVal} {ts : List (List FVal)} (h : Together (t :: ts)) :
    Together ts := by
  intro i j k hij hjk hk he
  have := h (i + 1) (j + 1) (k + 1) (by omega) (by omega) (by simpa using hk) (by simpa using he)
  simpa using this

/-- **Distinct accounts**: with each account's records together, the groups have distinct ids. -/
theorem groups_distinct_of_together : ∀ ts : List (List FVal), Together ts →
    (groups ts).Pairwise (fun g h => g.1 ≠ h.1)
  | [], _ => by simp [groups]
  | t :: ts, ht => by
    have ih := groups_distinct_of_together ts ht.tail
    have hfl := groups_flatten ts
    have hok := groups_ok ts
    unfold groups
    split
    · simp
    · rename_i id g rest h
      rw [h] at ih hfl hok
      have ihc := List.pairwise_cons.1 ih
      split
      · exact List.pairwise_cons.2 ⟨fun g' hg' => ihc.1 g' hg', ihc.2⟩
      · rename_i hid
        refine List.pairwise_cons.2 ⟨fun g' hg' => ?_, ih⟩
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact hid
        · intro he
          -- the first record of `g` lies between `t` and a record `r` of the later group `g'`
          obtain ⟨hne', hall'⟩ := hok g' (by simp [hg'])
          obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne'
          obtain ⟨hne, hall⟩ := hok (id, g) (by simp)
          have hg0 : 0 < g.length := List.length_pos_iff.2 hne
          obtain ⟨kr, hkr, hrk⟩ := List.mem_iff_getElem.1 (List.mem_flatMap.2 ⟨g', hg', hr⟩)
          have hts : ts = g ++ rest.flatMap Prod.snd := by rw [← hfl]; simp
          have e0 : (t :: ts).getD 0 [] = t := rfl
          have e1 : (t :: ts).getD 1 [] = g[0] := by
            rw [hts]
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hg0,
              List.getElem?_eq_getElem hg0]
          have e2 : (t :: ts).getD (g.length + kr + 1) [] = r := by
            rw [hts, List.getD_cons_succ, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
              List.getElem?_eq_getElem hkr, hrk]
            rfl
          have hlen : g.length + kr + 1 < (t :: ts).length := by
            rw [hts]; simp only [List.length_cons, List.length_append]; omega
          have h3 := ht 0 1 (g.length + kr + 1) (by omega) (by omega) hlen (by
            rw [e0, e2, hall' r hr]; exact he)
          rw [e0, e1, hall g[0] (List.getElem_mem hg0)] at h3
          exact hid h3.symm

theorem accsOf_distinct' {tcat xrefs accts : List (List FVal)} (h : Together tcat) :
    (accsOf tcat xrefs accts).Pairwise (fun a b => a.id ≠ b.id) := by
  simp only [accsOf, List.pairwise_map]
  exact groups_distinct_of_together tcat h

theorem accsOf_validIn {tcat xrefs accts : List (List FVal)}
    (hv : ∀ t ∈ tcat, TranCatBalRecord.Valid t) : ∀ a ∈ accsOf tcat xrefs accts, a.validIn := by
  intro a ha
  simp only [accsOf, List.mem_map] at ha
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨hne, hall⟩ := groups_ok tcat g hg
  have hmem : ∀ t ∈ g.2, t ∈ tcat := fun t ht => by
    rw [← groups_flatten tcat]; exact List.mem_flatMap.2 ⟨g, hg, ht⟩
  obtain ⟨t0, ht0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨-, -, hb, h0⟩ := catVals_catOf (hv t0 (hmem t0 ht0))
  rw [hall t0 ht0] at hb h0
  refine ⟨hb, h0, by simpa [accOf] using hne, fun c hc => ?_⟩
  simp only [accOf, List.mem_map] at hc
  obtain ⟨t, ht, rfl⟩ := hc
  exact (catVals_catOf (hv t (hmem t ht))).2.1

/-! ## The simulation -/

open CardDemo.Cbact04c (M4x step4x rateX acctIdx xrefIdx discIdx acc0 disc0 abendEvents4 txRecX)

/-- The translations' state `t` after the same category records as coblean's model state `s`;
`left` = the accounts rewritten so far. -/
structure Corr (accts : List (List FVal)) (t : StE) (s : M4x) (left : List Int) : Prop where
  stop : t.stop = s.stop
  last : t.lastId = s.last
  total : t.total = s.total
  k : t.k = s.k
  disp : t.disp = txt "START OF EXECUTION OF PROGRAM CBACT04C" :: dispOf s.out.reverse
  wr : t.writes.map some = wrOf s.out.reverse
  rw : t.rewrites.map some = rwOf s.out.reverse
  cur : s.stop = false → ∀ id, s.last = some id →
    AccountRecord.Valid t.acct ∧ aId t.acct = id ∧ s.acct = acctAcc t.acct ∧
      CardXrefRecord.Valid t.xref ∧ s.card = xCard t.xref
  tbl : ∀ id, id ∉ left → findAcctO t.accts id = findAcctO accts id

theorem Corr.mono {accts : List (List FVal)} {t : StE} {s : M4x} {left left' : List Int}
    (h : Corr accts t s left) (hl : ∀ x ∈ left, x ∈ left') : Corr accts t s left' :=
  { h with tbl := fun id hid => h.tbl id (fun hx => hid (hl id hx)) }

theorem txRecX_eq (parm dt fl : List UInt8) (clk : Nat → List UInt8) (k : Nat) (aid : Int)
    (card : List UInt8) (amt : Int) (hcard : card.length = 16) :
    txRecX parm dt fl clk k aid card amt =
      CardDemo.Cbact04c.txRec parm dt fl clk k { acc0 with id := aid, xrec := card } amt := by
  simp [txRecX, CardDemo.Cbact04c.txRec, List.take_of_length_le (by omega : card.length ≤ 16)]

theorem decode_txRecX (parm clk card : List UInt8) (k0 : Nat) (aid amt : Int)
    (hp : parm.length = 10) (hc : 16 ≤ clk.length) (hcl : card.length = 16) (hk : k0 + 1 < 1000000)
    (hid : aid.natAbs < 100000000000) (hamt : amt.natAbs < 100000000000) :
    TranRecord.decode (txRecX parm (sp 76) (sp 20) (fun _ => clk) k0 aid card amt) =
      some (tranVals parm clk (k0 + 1) aid card amt) := by
  rw [txRecX_eq _ _ _ _ _ _ _ _ hcl]
  exact decode_txRec parm clk card k0 _ amt
    (show card.take 16 = card from List.take_of_length_le (by omega)) hp hc hcl hk hid hamt

set_option maxHeartbeats 2000000 in
/-- The interest at rate `r` keeps `Corr`. -/
theorem interest_corr {accts : List (List FVal)} {parm clk : List UInt8} {t : StE} {s : M4x}
    {left : List Int} {id : Int} {c : Cat} (r : Int) (hC : Corr accts t s left)
    (hs : s.stop = false) (hl : s.last = some id) (hk : s.k + 1 < 1000000)
    (hparm : parm.length = 10) (hclk : 16 ≤ clk.length) :
    Corr accts (t.interest parm clk (catVals id c) r)
      (rateX.withRateX parm (sp 76) (sp 20) (fun _ => clk) s c r s.out) left := by
  obtain ⟨hA, haid, hsa, hX, hcard⟩ := hC.cur hs id hl
  unfold StE.interest rateX.withRateX
  by_cases hr : r = 0
  · simp only [hr, ↓reduceIte]
    exact hC
  · simp only [hr, ↓reduceIte]
    obtain ⟨i, s', bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, hAe, hidb, -⟩ := acct_shape hA
    have hcard16 : (xCard t.xref).length = 16 := by
      obtain ⟨card, cust, acct, fill, hXe, hc16, -⟩ := xref_shape hX
      rw [hXe]; exact hc16
    have hidb' : (aId t.acct).natAbs < 100000000000 := by rw [hAe]; exact hidb
    have hkk : (t.k + 1) % 1000000 = s.k + 1 := by rw [hC.k]; exact Nat.mod_eq_of_lt hk
    have hamt : Int.tmod (Int.tdiv (tBal (catVals id c) * r) 120000) (10 ^ 11) =
        CardDemo.Cbact04c.monthly c r := by rw [monthly_eq]; rfl
    have hamtb : (CardDemo.Cbact04c.monthly c r).natAbs < 100000000000 := by
      rw [monthly_eq, Int.natAbs_tmod]; exact Nat.mod_lt _ (by decide)
    refine ⟨hC.stop, hC.last, ?_, hkk, ?_, ?_, ?_, ?_, hC.tbl⟩
    · rw [hamt, total_eq, hC.total]
    · simp [hC.disp, dispOf]
    · rw [hkk, hamt]
      simp only [List.map_append, hC.wr, List.reverse_cons, wrOf_append]
      rw [hsa, hcard]
      simp [wrOf, decode_txRecX parm clk _ s.k _ _ hparm hclk hcard16 hk hidb' hamtb, acctAcc,
        accOf, findAcct_single]
    · simp [hC.rw, rwOf]
    · intro _ id' hl'
      exact hC.cur hs id' hl'


theorem dispOf_displays (bss : List (List UInt8)) :
    dispOf (bss.map Event.display) = bss.map (·.map cp037Code) := by
  induction bss with
  | nil => rfl
  | cons b bs ih =>
    rw [List.map_cons, show Event.display b :: bs.map Event.display =
      [Event.display b] ++ bs.map Event.display from rfl, dispOf_append, ih]
    rfl

theorem wrOf_displays (bss : List (List UInt8)) : wrOf (bss.map Event.display) = [] := by
  induction bss with
  | nil => rfl
  | cons b bs ih =>
    rw [List.map_cons, show Event.display b :: bs.map Event.display =
      [Event.display b] ++ bs.map Event.display from rfl, wrOf_append, ih]
    rfl

theorem rwOf_displays (bss : List (List UInt8)) : rwOf (bss.map Event.display) = [] := by
  induction bss with
  | nil => rfl
  | cons b bs ih =>
    rw [List.map_cons, show Event.display b :: bs.map Event.display =
      [Event.display b] ++ bs.map Event.display from rfl, rwOf_append, ih]
    rfl

/-- `DISPLAY`s keep `Corr`. -/
theorem Corr.displays {accts : List (List FVal)} {t : StE} {s : M4x} {left : List Int}
    (hC : Corr accts t s left) (bss : List (List UInt8)) :
    Corr accts { t with disp := t.disp ++ bss.map (·.map cp037Code) }
      { s with out := (bss.map Event.display).reverse ++ s.out } left := by
  have hd := dispOf_displays bss
  have hw := wrOf_displays bss
  have hr := rwOf_displays bss
  refine ⟨hC.stop, hC.last, hC.total, hC.k, ?_, ?_, ?_, hC.cur, hC.tbl⟩
  · simp only [List.reverse_append, List.reverse_reverse, dispOf_append, hd, hC.disp,
      List.cons_append]
  · simp only [List.reverse_append, List.reverse_reverse, wrOf_append, hw, hC.wr, List.append_nil]
  · simp only [List.reverse_append, List.reverse_reverse, rwOf_append, hr, hC.rw, List.append_nil]

/-- An abend after the lines `pre` and the error line `msg` keeps `Corr`. -/
theorem Corr.abend {accts : List (List FVal)} {t : StE} {s : M4x} {left : List Int}
    (hC : Corr accts t s left) (pre : List (List UInt8)) (msg : List UInt8) :
    Corr accts (t.abend ((pre ++ [msg]).map (·.map cp037Code)))
      { s with out := abendEvents4 msg ++ ((pre.map Event.display).reverse ++ s.out),
               stop := true } left := by
  have h := hC.displays (pre ++ [msg, CardDemo.Cbact04c.status23Msg, CardDemo.Cbact04c.abendMsg])
  have e1 : (abendEvents4 msg ++ ((pre.map Event.display).reverse ++ s.out)) =
      ((pre ++ [msg, CardDemo.Cbact04c.status23Msg, CardDemo.Cbact04c.abendMsg]).map
        Event.display).reverse ++ s.out := by
    simp [abendEvents4, List.reverse_append]
  have e2 : t.disp ++ (pre ++ [msg]).map (·.map cp037Code) ++
      [txt "FILE STATUS IS: NNNN0023", txt "ABENDING PROGRAM"] =
      t.disp ++ (pre ++ [msg, CardDemo.Cbact04c.status23Msg, CardDemo.Cbact04c.abendMsg]).map
        (·.map cp037Code) := by
    simp [status23_text, abend_text]
  obtain ⟨_, h2, h3, h4, h5, h6, h7, -, h9⟩ := h
  refine ⟨rfl, h2, h3, h4, ?_, ?_, ?_, (fun hs => by cases hs), h9⟩
  · simp only [StE.abend]; rw [e1, e2]; exact h5
  · simp only [StE.abend]; rw [e1]; exact h6
  · simp only [StE.abend]; rw [e1]; exact h7

theorem withRateX_out (parm dt fl : List UInt8) (clk : Nat → List UInt8) (s : M4x) (c : Cat)
    (r : Int) (out : List Event) :
    rateX.withRateX parm dt fl clk s c r out =
      rateX.withRateX parm dt fl clk { s with out := out } c r out := by
  unfold rateX.withRateX
  split <;> rfl

theorem rateX_out (discs : List Disc) (parm dt fl : List UInt8) (clk : Nat → List UInt8) (s : M4x)
    (c : Cat) (out : List Event) :
    rateX discs parm dt fl clk s c out = rateX discs parm dt fl clk { s with out := out } c out := by
  cases s; rfl

set_option maxHeartbeats 2000000 in
/-- The rate (the account's disclosure group, else group `DEFAULT`, else an abend) and the
interest keep `Corr`. -/
theorem rate_corr {accts discs : List (List FVal)} {parm clk : List UInt8} {t : StE} {s : M4x}
    {left : List Int} {id : Int} {c : Cat} (hv4 : ∀ D ∈ discs, DisGroupRecord.Valid D)
    (hC : Corr accts t s left) (hs : s.stop = false) (hl : s.last = some id) (hc : c.valid)
    (hk : s.k + 1 < 1000000) (hparm : parm.length = 10) (hclk : 16 ≤ clk.length) :
    Corr accts (t.rate discs parm clk (catVals id c))
      (rateX (discs.map discOf) parm (sp 76) (sp 20) (fun _ => clk) s c s.out) left := by
  obtain ⟨hA, -, hsa, -, -⟩ := hC.cur hs id hl
  have hgl : (aGrp t.acct).length = 10 := by
    obtain ⟨i, s', bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, hAe, -, -, -, -, -, -, -, -, -,
      -, -, -, hg, -⟩ := acct_shape hA
    rw [hAe]; exact hg
  have hE := discIdx_eq hv4 hgl hc
  have hE2 := discIdx_eq hv4 (grp := defaultGrp) (by decide) hc
  have hty : tType (catVals id c) = c.ty := rfl
  have hcat : tCat (catVals id c) = c.cat := rfl
  unfold StE.rate rateX
  rw [hsa, acctAcc_grp, hty, hcat, defaultGrp_eq]
  cases hd : discIdx (discs.map discOf) (aGrp t.acct) c with
  | some i =>
    rw [hd, Option.map_some] at hE
    rw [← hE]
    exact interest_corr _ hC hs hl hk hparm hclk
  | none =>
    rw [hd, Option.map_none] at hE
    rw [← hE]
    dsimp only
    have h1 := hC.displays [CardDemo.Cbact04c.missingMsg, CardDemo.Cbact04c.tryDefaultMsg]
    simp only [List.map_cons, List.map_nil, missing_text, tryDefault_text] at h1
    cases hd2 : discIdx (discs.map discOf) defaultGrp c with
    | some i =>
      rw [hd2, Option.map_some] at hE2
      rw [← hE2]
      dsimp only
      rw [withRateX_out]
      exact interest_corr _ h1 hs hl hk hparm hclk
    | none =>
      rw [hd2, Option.map_none] at hE2
      rw [← hE2]
      dsimp only
      have h2 := h1.abend [] CardDemo.Cbact04c.errDefaultMsg
      simp only [List.nil_append, List.map_cons, List.map_nil, errDefault_text, List.reverse_nil]
        at h2
      rw [hsa] at h2
      exact h2


theorem findAcctO_replaceFirst (j i : Int) (p : List FVal) (hp : aId p = j) (hij : i ≠ j) :
    ∀ tbl : List (List FVal),
      findAcctO (replaceFirst (fun a => aId a == j) p tbl) i = findAcctO tbl i
  | [] => rfl
  | y :: ys => by
    have ih := findAcctO_replaceFirst j i p hp hij ys
    unfold findAcctO at ih ⊢
    simp only [replaceFirst]
    by_cases hy : aId y = j
    · have hji : (j == i) = false := by simp [Ne.symm hij]
      simp [hy, hp, hji]
    · have hy' : (aId y == j) = false := by simp [hy]
      simp only [hy', Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      split <;> simp_all

/-- The `REWRITE` of the current account keeps `Corr`, with its id among the accounts left. -/
theorem rewrite_corr {accts : List (List FVal)} {t : StE} {s : M4x} {left : List Int} {l : Int}
    (hC : Corr accts t s left) (hs : s.stop = false) (hl : s.last = some l) :
    Corr accts
      { t with accts := replaceFirst (fun b => aId b == aId t.acct) (posted t.acct t.total) t.accts,
               rewrites := t.rewrites ++ [posted t.acct t.total] }
      { s with out := .rewrite 3 (s.acct.posted s.total) :: s.out } (l :: left) := by
  obtain ⟨hA, haid, hsa, -, -⟩ := hC.cur hs l hl
  have hpa : aId (posted t.acct t.total) = l := by rw [aId_posted, haid]
  refine ⟨hC.stop, hC.last, hC.total, hC.k, ?_, ?_, ?_, hC.cur, ?_⟩
  · simp [hC.disp, dispOf]
  · simp [hC.wr, wrOf]
  · simp only [List.map_append, hC.rw, List.reverse_cons, rwOf_append]
    simp [rwOf, hsa, decode_acctAcc_posted hA, hC.total]
  · intro id hid
    simp only [List.mem_cons, not_or] at hid
    rw [haid, findAcctO_replaceFirst l id _ hpa hid.1, hC.tbl id hid.2]

/-- The translations' step after the display and the rewrite: the reads, then the rate. -/
def tailE (xrefs discs : List (List FVal)) (parm clk : List UInt8) (s2 : StE) (t : List FVal) :
    StE :=
  match findAcctO s2.accts (tAcct t) with
  | none => s2.abend [txt "ACCOUNT NOT FOUND: " ++ zpad 11 (tAcct t).natAbs,
      txt "ERROR READING ACCOUNT FILE"]
  | some a =>
    match findXrefO xrefs (tAcct t) with
    | none => s2.abend [txt "ACCOUNT NOT FOUND: " ++ zpad 11 (tAcct t).natAbs,
        txt "ERROR READING XREF FILE"]
    | some x =>
      ({ s2 with lastId := some (tAcct t), total := 0, acct := a, xref := x } : StE).rate
        discs parm clk t

theorem stepE_eq (xrefs discs : List (List FVal)) (parm clk : List UInt8) (s : StE)
    (t : List FVal) :
    stepE xrefs discs parm clk s t =
      if s.stop then s
      else if s.lastId = some (tAcct t) then
        ({ s with disp := s.disp ++ [TranCatBalRecord.textS t] } : StE).rate discs parm clk t
      else
        tailE xrefs discs parm clk
          (if s.lastId.isSome then
            { s with disp := s.disp ++ [TranCatBalRecord.textS t],
                     accts := replaceFirst (fun a => aId a == aId s.acct) (posted s.acct s.total)
                       s.accts,
                     rewrites := s.rewrites ++ [posted s.acct s.total] }
          else { s with disp := s.disp ++ [TranCatBalRecord.textS t] }) t := rfl

/-- coblean's step after the display and the rewrite: the reads, then the rate. -/
def tail4x (accts : List Acc) (xrefs : List (List UInt8)) (discs : List Disc)
    (parm dt fl : List UInt8) (clk : Nat → List UInt8) (s : CardDemo.Cbact04c.M4x) (p : Acc × Cat)
    (out2 : List Event) : CardDemo.Cbact04c.M4x :=
  match acctIdx accts p.1.id with
  | none => { s with out := (abendEvents4 CardDemo.Cbact04c.errAcctMsg ++
      Event.display (CardDemo.Cbact04c.notFoundMsg ++
        encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt p.1.id) :: out2), stop := true }
  | some i =>
    match xrefIdx xrefs p.1.id with
    | none => { s with out := (abendEvents4 CardDemo.Cbact04c.errXrefMsg ++
        Event.display (CardDemo.Cbact04c.notFoundMsg ++
          encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt p.1.id) :: out2), stop := true }
    | some j =>
      rateX discs parm dt fl clk
        { s with last := some p.1.id, acct := accts.getD i acc0, card := (xrefs.getD j []).take 16,
                 total := 0 } p.2 out2

theorem step4x_eq (accts : List Acc) (xrefs : List (List UInt8)) (discs : List Disc)
    (parm dt fl : List UInt8) (clk : Nat → List UInt8) (s : CardDemo.Cbact04c.M4x) (p : Acc × Cat) :
    step4x accts xrefs discs parm dt fl clk s p =
      if s.stop then s
      else if s.last = some p.1.id then
        rateX discs parm dt fl clk s p.2 (.display (Cat.bytes p.1.id p.2) :: s.out)
      else
        tail4x accts xrefs discs parm dt fl clk s p
          (if s.last.isSome then
            Event.rewrite 3 (s.acct.posted s.total) :: Event.display (Cat.bytes p.1.id p.2) :: s.out
          else Event.display (Cat.bytes p.1.id p.2) :: s.out) := rfl

set_option maxHeartbeats 4000000 in
/-- The reads of a new account (an abend if one fails) and the rate keep `Corr`. -/
theorem lookup_corr {xrefs accts discs : List (List FVal)} {parm clk : List UInt8} {t2 : StE}
    {s : CardDemo.Cbact04c.M4x} {out2 : List Event} {left : List Int} {a : Acc} {c : Cat}
    (hv2 : ∀ X ∈ xrefs, CardXrefRecord.Valid X) (hv3 : ∀ A ∈ accts, AccountRecord.Valid A)
    (hv4 : ∀ D ∈ discs, DisGroupRecord.Valid D)
    (hC : Corr accts t2 { s with out := out2 } left) (hs : s.stop = false) (hfr : a.id ∉ left)
    (hc : c.valid) (hid : a.id.natAbs < 100000000000) (hid0 : 0 ≤ a.id)
    (hk : s.k + 1 < 1000000) (hparm : parm.length = 10) (hclk : 16 ≤ clk.length) :
    Corr accts (tailE xrefs discs parm clk t2 (catVals a.id c))
      (tail4x (accts.map acctAcc) (xrefs.map CardXrefRecord.encode) (discs.map discOf) parm
        (sp 76) (sp 20) (fun _ => clk) s (a, c) out2) left := by
  have ht : tAcct (catVals a.id c) = a.id := rfl
  have hA := acctIdx_eq hv3 (id := a.id) ((holds_display rfl).2 ⟨hid, fun _ => hid0⟩)
  have hX := xrefIdx_eq hv2 (id := a.id) ((holds_display rfl).2 ⟨hid, fun _ => hid0⟩)
  have htbl := hC.tbl a.id hfr
  unfold tailE tail4x
  dsimp only
  rw [ht, htbl]
  cases hfa : findAcctO accts a.id with
  | none =>
    rw [hfa] at hA
    cases hai : acctIdx (accts.map acctAcc) a.id with
    | some i => rw [hai] at hA; cases hA
    | none =>
      dsimp only
      have h := hC.abend [CardDemo.Cbact04c.notFoundMsg ++
        encodeNum {} CardDemo.Cbact04c.FD_ACCT_ID.fmt a.id] CardDemo.Cbact04c.errAcctMsg
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        notFound_acct_text, errAcct_text, List.reverse_cons, List.reverse_nil] at h
      exact h
  | some A =>
    rw [hfa] at hA
    have hAm : A ∈ accts := List.mem_of_find?_eq_some hfa
    have hAid : aId A = a.id := by simpa using List.find?_some hfa
    cases hai : acctIdx (accts.map acctAcc) a.id with
    | none => rw [hai] at hA; cases hA
    | some i =>
      simp only [hai, Option.map_some, Option.some.injEq] at hA
      dsimp only
      cases hfx : findXrefO xrefs a.id with
      | none =>
        rw [hfx] at hX
        cases hxj : xrefIdx (xrefs.map CardXrefRecord.encode) a.id with
        | some j => rw [hxj] at hX; cases hX
        | none =>
          dsimp only
          have h := hC.abend [CardDemo.Cbact04c.notFoundMsg ++
            encodeNum {} CardDemo.Cbact04c.FD_XREF_ACCT_ID.fmt a.id] CardDemo.Cbact04c.errXrefMsg
          simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
            notFound_xref_text, errXref_text, List.reverse_cons, List.reverse_nil] at h
          exact h
      | some X =>
        rw [hfx] at hX
        have hXm : X ∈ xrefs := List.mem_of_find?_eq_some hfx
        cases hxj : xrefIdx (xrefs.map CardXrefRecord.encode) a.id with
        | none => rw [hxj] at hX; cases hX
        | some j =>
          simp only [hxj, Option.map_some, Option.some.injEq] at hX
          dsimp only
          rw [hA, hX, rateX_out]
          have hC3 : Corr accts { t2 with lastId := some a.id, total := 0, acct := A, xref := X }
              { s with last := some a.id, acct := acctAcc A, card := xCard X, total := 0,
                       out := out2 } left :=
            ⟨hC.stop, rfl, rfl, hC.k, hC.disp, hC.wr, hC.rw,
              fun _ id' hl' => by
                cases hl'
                exact ⟨hv3 A hAm, hAid, rfl, hv2 X hXm, rfl⟩, hC.tbl⟩
          exact rate_corr hv4 hC3 hs rfl hc hk hparm hclk

/-- The accounts rewritten after one more record of account `aid`. -/
def leftAfterX (s : CardDemo.Cbact04c.M4x) (aid : Int) (left : List Int) : List Int :=
  match s.last with
  | some l => if l = aid then left else l :: left
  | none => left

set_option maxHeartbeats 4000000 in
/-- **One category record**: the translations' step and coblean's `step4x` keep `Corr`. -/
theorem step_corr {xrefs accts discs : List (List FVal)} {parm clk : List UInt8} {t : StE}
    {s : CardDemo.Cbact04c.M4x} {left : List Int} {a : Acc} {c : Cat}
    (hv2 : ∀ X ∈ xrefs, CardXrefRecord.Valid X) (hv3 : ∀ A ∈ accts, AccountRecord.Valid A)
    (hv4 : ∀ D ∈ discs, DisGroupRecord.Valid D) (hC : Corr accts t s left) (hc : c.valid)
    (hid : a.id.natAbs < 100000000000) (hid0 : 0 ≤ a.id)
    (hfresh : s.last ≠ some a.id → a.id ∉ left) (hk : s.k + 1 < 1000000)
    (hparm : parm.length = 10) (hclk : 16 ≤ clk.length) :
    Corr accts (stepE xrefs discs parm clk t (catVals a.id c))
      (step4x (accts.map acctAcc) (xrefs.map CardXrefRecord.encode) (discs.map discOf) parm
        (sp 76) (sp 20) (fun _ => clk) s (a, c)) (leftAfterX s a.id left) := by
  have htext := catVals_text a.id c hc hid hid0
  rw [stepE_eq, step4x_eq]
  dsimp only
  have hleft : ∀ x ∈ left, x ∈ leftAfterX s a.id left := by
    intro x hx; unfold leftAfterX; split
    · split <;> simp [hx]
    · exact hx
  cases hs : s.stop with
  | true =>
    have hts : t.stop = true := by rw [hC.stop, hs]
    rw [ite_eq_left hts, ite_eq_left (show true = true from rfl)]
    exact hC.mono hleft
  | false =>
    have hts : ¬ t.stop = true := by rw [hC.stop, hs]; decide
    rw [ite_eq_right hts, ite_eq_right (show ¬ (false = true) by decide)]
    have h1 := hC.displays [Cat.bytes a.id c]
    simp only [List.map_cons, List.map_nil, ← htext, List.reverse_singleton,
      List.singleton_append] at h1
    by_cases hsame : s.last = some a.id
    · have htl : t.lastId = some (tAcct (catVals a.id c)) := by rw [hC.last, hsame]; rfl
      have hla : leftAfterX s a.id left = left := by simp [leftAfterX, hsame]
      rw [ite_eq_left htl, ite_eq_left hsame, hla, rateX_out]
      exact rate_corr hv4 h1 hs hsame hc hk hparm hclk
    · have htl : ¬ t.lastId = some (tAcct (catVals a.id c)) := by
        rw [hC.last]; exact hsame
      rw [ite_eq_right htl, ite_eq_right hsame]
      have hfr := hfresh hsame
      cases hlast : s.last with
      | none =>
        have htn : ¬ t.lastId.isSome = true := by rw [hC.last, hlast]; decide
        have hla : leftAfterX s a.id left = left := by simp [leftAfterX, hlast]
        rw [ite_eq_right htn, ite_eq_right (show ¬ ((none : Option Int).isSome = true) by decide),
          hla]
        exact lookup_corr hv2 hv3 hv4 h1 hs hfr hc hid hid0 hk hparm hclk
      | some l =>
        have hl : l ≠ a.id := fun h => hsame (by rw [hlast, h])
        have htn : t.lastId.isSome = true := by rw [hC.last, hlast]; rfl
        have hla : leftAfterX s a.id left = l :: left := by simp [leftAfterX, hlast, hl]
        rw [ite_eq_left htn, ite_eq_left (show (some l).isSome = true from rfl), hla]
        exact lookup_corr hv2 hv3 hv4 (rewrite_corr h1 hs hlast) hs (by simp [Ne.symm hl, hfr]) hc
          hid hid0 hk hparm hclk

theorem rateX_last (discs : List Disc) (parm dt fl : List UInt8) (clk : Nat → List UInt8)
    (s : CardDemo.Cbact04c.M4x) (c : Cat) (out : List Event) :
    (rateX discs parm dt fl clk s c out).last = s.last := by
  simp only [rateX, rateX.withRateX]
  repeat' split
  all_goals rfl

theorem step4x_last (accts : List Acc) (xrefs : List (List UInt8)) (discs : List Disc)
    (parm dt fl : List UInt8) (clk : Nat → List UInt8) (s : CardDemo.Cbact04c.M4x) (p : Acc × Cat) :
    (step4x accts xrefs discs parm dt fl clk s p).last = s.last ∨
      (step4x accts xrefs discs parm dt fl clk s p).last = some p.1.id := by
  rw [step4x_eq]
  split
  · exact .inl rfl
  split
  · exact .inl (rateX_last ..)
  unfold tail4x
  split
  · exact .inl rfl
  split
  · exact .inl rfl
  · exact .inr (rateX_last ..)

/-- The records of one account `a`. -/
theorem cats_corr {xrefs accts discs : List (List FVal)} {parm clk : List UInt8} {a : Acc}
    (hv2 : ∀ X ∈ xrefs, CardXrefRecord.Valid X) (hv3 : ∀ A ∈ accts, AccountRecord.Valid A)
    (hv4 : ∀ D ∈ discs, DisGroupRecord.Valid D) (hid : a.id.natAbs < 100000000000)
    (hid0 : 0 ≤ a.id) (hparm : parm.length = 10) (hclk : 16 ≤ clk.length) :
    ∀ (cs : List Cat) (t : StE) (s : CardDemo.Cbact04c.M4x) (left : List Int),
      (∀ c ∈ cs, c.valid) → Corr accts t s left →
      (s.last ≠ some a.id → a.id ∉ left) → s.k + cs.length < 999999 →
      ∃ left', Corr accts (cs.foldl (fun t c => stepE xrefs discs parm clk t (catVals a.id c)) t)
          (cs.foldl (fun s c => step4x (accts.map acctAcc) (xrefs.map CardXrefRecord.encode)
            (discs.map discOf) parm (sp 76) (sp 20) (fun _ => clk) s (a, c)) s) left' ∧
        ((cs.foldl (fun s c => step4x (accts.map acctAcc) (xrefs.map CardXrefRecord.encode)
            (discs.map discOf) parm (sp 76) (sp 20) (fun _ => clk) s (a, c)) s).last = s.last ∨
          (cs.foldl (fun s c => step4x (accts.map acctAcc) (xrefs.map CardXrefRecord.encode)
            (discs.map discOf) parm (sp 76) (sp 20) (fun _ => clk) s (a, c)) s).last = some a.id) ∧
        (cs.foldl (fun s c => step4x (accts.map acctAcc) (xrefs.map CardXrefRecord.encode)
            (discs.map discOf) parm (sp 76) (sp 20) (fun _ => clk) s (a, c)) s).k ≤ s.k + cs.length ∧
        (∀ x ∈ left', x ∈ left ∨ s.last = some x ∨ x = a.id)
  | [], t, s, left, _, hC, _, _ => ⟨left, hC, .inl rfl, by simp, fun x hx => .inl hx⟩
  | c :: cs, t, s, left, hcs, hC, hfresh, hk => by
    have h1 := step_corr (discs := discs) (parm := parm) (clk := clk) hv2 hv3 hv4 hC
      (hcs c (by simp)) hid hid0 hfresh (by simp at hk; omega) hparm hclk
    have hl1 := step4x_last (accts.map acctAcc) (xrefs.map CardXrefRecord.encode)
      (discs.map discOf) parm (sp 76) (sp 20) (fun _ => clk) s (a, c)
    have hk1 := CardDemo.Cbact04c.step4x_k_le (accts.map acctAcc)
      (xrefs.map CardXrefRecord.encode) (discs.map discOf) parm (sp 76) (sp 20) (fun _ => clk) s (a, c)
    have hfr1 : (step4x (accts.map acctAcc) (xrefs.map CardXrefRecord.encode) (discs.map discOf)
        parm (sp 76) (sp 20) (fun _ => clk) s (a, c)).last ≠ some a.id →
        a.id ∉ leftAfterX s a.id left := by
      intro hne
      unfold leftAfterX
      cases hs : s.last with
      | none => exact hfresh (by rw [hs]; simp)
      | some l =>
        by_cases hla : l = a.id
        · subst hla
          rcases hl1 with h | h <;> rw [h] at hne
          · exact absurd hs hne
          · exact absurd rfl hne
        · simp only [hla, ↓reduceIte, List.mem_cons, not_or]
          exact ⟨fun h => hla h.symm, hfresh (by rw [hs]; simpa using hla)⟩
    obtain ⟨left', hC', hlast', hk', hsub⟩ := cats_corr hv2 hv3 hv4 hid hid0 hparm hclk cs _ _ _
      (fun c' hc' => hcs c' (by simp [hc'])) h1 hfr1 (by simp at hk; omega)
    refine ⟨left', hC', ?_, ?_, ?_⟩
    · simp only [List.foldl_cons]
      rcases hlast' with h | h
      · rw [h]; exact hl1
      · exact .inr h
    · simp only [List.foldl_cons, List.length_cons]; omega
    · intro x hx
      rcases hsub x hx with h | h | h
      · unfold leftAfterX at h
        cases hs : s.last with
        | none => rw [hs] at h; exact .inl h
        | some l =>
          rw [hs] at h
          by_cases hla : l = a.id
          · simp only [hla, ↓reduceIte] at h; exact .inl h
          · simp only [hla, ↓reduceIte, List.mem_cons] at h
            rcases h with rfl | h
            · exact .inr (.inl rfl)
            · exact .inl h
      · rcases hl1 with h' | h'
        · rw [h'] at h; exact .inr (.inl h)
        · rw [h'] at h; simp at h; exact .inr (.inr h.symm)
      · exact .inr (.inr h)

/-- The records of the accounts `rest`, from a state that has seen none of them. -/
theorem accs_corr {xrefs accts discs : List (List FVal)} {parm clk : List UInt8}
    (hv2 : ∀ X ∈ xrefs, CardXrefRecord.Valid X) (hv3 : ∀ A ∈ accts, AccountRecord.Valid A)
    (hv4 : ∀ D ∈ discs, DisGroupRecord.Valid D) (hparm : parm.length = 10)
    (hclk : 16 ≤ clk.length) :
    ∀ (rest : List Acc) (t : StE) (s : CardDemo.Cbact04c.M4x) (left : List Int),
      Corr accts t s left →
      (∀ b ∈ rest, b.id ∉ left ∧ s.last ≠ some b.id) →
      rest.Pairwise (fun a b => a.id ≠ b.id) → (∀ b ∈ rest, b.validIn) →
      s.k + (CardDemo.Cbact04c.items rest).length < 999999 →
      ∃ left', Corr accts
        ((CardDemo.Cbact04c.items rest).foldl
          (fun t p => stepE xrefs discs parm clk t (catVals p.1.id p.2)) t)
        ((CardDemo.Cbact04c.items rest).foldl
          (step4x (accts.map acctAcc) (xrefs.map CardXrefRecord.encode) (discs.map discOf) parm
            (sp 76) (sp 20) (fun _ => clk)) s) left'
  | [], t, s, left, hC, _, _, _, _ => ⟨left, hC⟩
  | a :: rest, t, s, left, hC, hfr, hpw, hok, hk => by
    obtain ⟨hid, hid0, -, hcs⟩ := hok a (by simp)
    simp only [CardDemo.Cbact04c.items, List.flatMap_cons, List.foldl_append] at hk ⊢
    rw [List.length_append] at hk
    simp only [List.foldl_map]
    obtain ⟨left', hC', hlast, hk', hsub⟩ := cats_corr (discs := discs) hv2 hv3 hv4 hid hid0
      hparm hclk a.cats t s left hcs hC (fun _ => (hfr a (by simp)).1) (by simp at hk; omega)
    have hpw' := List.pairwise_cons.1 hpw
    exact accs_corr hv2 hv3 hv4 hparm hclk rest _ _ left' hC'
      (fun b hb => by
        obtain ⟨hbl, hbm⟩ := hfr b (by simp [hb])
        have hab : a.id ≠ b.id := hpw'.1 b hb
        refine ⟨fun hx => ?_, ?_⟩
        · rcases hsub b.id hx with h | h | h
          · exact hbl h
          · exact hbm h
          · exact hab h.symm
        · rcases hlast with h | h
          · rw [h]; exact hbm
          · rw [h]; simpa using hab)
      hpw'.2 (fun b hb => hok b (by simp [hb]))
      (by simp only [List.length_map] at hk; simp only [CardDemo.Cbact04c.items]; omega)

/-- **The translations' outputs are coblean's events**, for the category records of accounts
`accs` with distinct ids and fewer than 999999 records, on every account, cross-reference and
disclosure group file. -/
theorem run_corr {xrefs accts discs : List (List FVal)} {parm clk : List UInt8}
    (hv2 : ∀ X ∈ xrefs, CardXrefRecord.Valid X) (hv3 : ∀ A ∈ accts, AccountRecord.Valid A)
    (hv4 : ∀ D ∈ discs, DisGroupRecord.Valid D) (hparm : parm.length = 10)
    (hclk : 16 ≤ clk.length) (accs : List Acc) (hval : ∀ a ∈ accs, a.validIn)
    (hd : accs.Pairwise (fun a b => a.id ≠ b.id))
    (hn : (CardDemo.Cbact04c.items accs).length < 999999) :
    let o := runE ((CardDemo.Cbact04c.items accs).map (fun p => catVals p.1.id p.2)) xrefs accts
      discs parm clk
    let s := CardDemo.Cbact04c.model4x (accts.map acctAcc) (xrefs.map CardXrefRecord.encode)
      (discs.map discOf) parm (sp 76) (sp 20) (fun _ => clk) (CardDemo.Cbact04c.items accs)
    o.abended = s.stop ∧
      o.disp = txt "START OF EXECUTION OF PROGRAM CBACT04C" :: dispOf s.out.reverse ++
        (if s.stop then [] else [txt "END OF EXECUTION OF PROGRAM CBACT04C"]) ∧
      o.writes.map some = wrOf s.out.reverse ∧ o.rewrites.map some = rwOf s.out.reverse := by
  intro o s
  have h0 : Corr accts (initE accts) ⟨none, acc0, [], 0, 0, [], false⟩ [] :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (fun _ _ h => by cases h), fun _ _ => rfl⟩
  obtain ⟨left', hC⟩ := accs_corr (discs := discs) (parm := parm) (clk := clk) hv2 hv3 hv4 hparm hclk
    accs _ _ [] h0 (fun b _ => ⟨by simp, by simp⟩) hd hval (by simpa using hn)
  simp only [o, s, runE, CardDemo.Cbact04c.model4x, List.foldl_map]
  refine ⟨hC.stop, ?_, hC.wr, hC.rw⟩
  rw [← hC.stop]
  split
  · rw [hC.disp, List.append_nil]
  · rw [hC.disp]


/-! ## The COBOL run -/

set_option maxHeartbeats 4000000 in
/-- **CBACT04C's COBOL run outputs what `Model.runE` says**, for every input of the statement's
domain: valid field values, each account's category records together (fewer than 999999), a
`CURRENT-DATE` clock reading, the linkage record in the harness storage.  The account,
cross-reference and disclosure group files are arbitrary: a failed read abends (999). -/
theorem cobol_outputs (vals1 vals2 vals3 vals4 : List (List FVal)) (link1 : List FVal)
    (clk : List UInt8)
    (hv1 : ∀ v ∈ vals1, TranCatBalRecord.Valid v) (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, AccountRecord.Valid v) (hv4 : ∀ v ∈ vals4, DisGroupRecord.Valid v)
    (hl : ExternalParms.Valid link1) (hc : CurrentDate clk)
    (hD : Every.Domain vals1 vals2 vals3 vals4 link1) (n : Nat) (hn : vals1.length < n) :
    let r := CardDemo.Cbact04c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
          (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])
    let o := Model.runE vals1 vals2 vals3 vals4 (parmOf link1) clk
    (r.1 = .stop .goback ∨ r.1 = .fault (.abend 999)) ∧
      (displays r.2).map (·.map cp037Code) = o.disp ∧
      (writes 5 r.2).map TranRecord.decode = o.writes.map some ∧
      (rewrites 3 r.2).map AccountRecord.decode = o.rewrites.map some ∧
      abended r.1 = o.abended := by
  dsimp only
  have hval := accsOf_validIn (xrefs := vals2) (accts := vals3) hv1
  have hdist := accsOf_distinct' (xrefs := vals2) (accts := vals3) hD.2
  have hitems := items_accsOf (xrefs := vals2) (accts := vals3) hv1
  have hlen := length_items_accsOf (xrefs := vals2) (accts := vals3) hv1
  obtain ⟨hm, hparm, hdesc, hfill⟩ := mem_facts hl
  have hclk : ∀ k : Nat, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ (fun _ => clk) k = pre ++ encodeNum {} { digits := 2 } mil ++ post :=
    fun _ => clock_ok hc
  have hfile1 : vals1.map TranCatBalRecord.encode =
      (CardDemo.Cbact04c.items (accsOf vals1 vals2 vals3)).map (fun p => Cat.bytes p.1.id p.2) := by
    conv => lhs; rw [← hitems]
    rw [List.map_map]
    exact List.map_congr_left fun p _ => catVals_encode _ _
  have hfile3 : vals3.map AccountRecord.encode = (vals3.map acctAcc).map Acc.bytes := by
    rw [List.map_map]; exact List.map_congr_left fun A hA => (acctAcc_bytes (hv3 A hA)).symm
  have hfile4 : vals4.map DisGroupRecord.encode = (vals4.map discOf).map Disc.bytes := by
    rw [List.map_map]; exact List.map_congr_left fun D hD => (discOf_bytes (hv4 D hD)).symm
  -- coblean's theorem, for the accounts of the input and the three files as they are
  have hev := CardDemo.Cbact04c.cbact04c_every
    (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1)) hm (fun _ => clk) hclk
    (accsOf vals1 vals2 vals3) hval hdist (by rw [hlen]; exact hD.1)
    (vals3.map acctAcc) (fun a ha => by
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 ha; exact acctAcc_validRec (hv3 A hA))
    (vals2.map CardXrefRecord.encode) (fun x hx => by
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx; exact Schema.length_encode (by decide) (hv2 X hX))
    (vals4.map discOf) (fun d hd => by
      obtain ⟨D, hD', rfl⟩ := List.mem_map.1 hd; exact discOf_valid (hv4 D hD'))
    n (by rw [hlen]; exact hn)
  simp only [hparm, hdesc, hfill] at hev
  rw [← hfile1, ← hfile3, ← hfile4] at hev
  -- the translations' model, for the same accounts
  obtain ⟨ho1, ho2, ho3, ho4⟩ := run_corr (xrefs := vals2) (accts := vals3) (discs := vals4)
    (parm := parmOf link1) (clk := clk) hv2 hv3 hv4
    (by obtain ⟨_, _, rfl, hd, _⟩ := link_shape hl; exact hd) (by rw [hc.1]; decide)
    (accsOf vals1 vals2 vals3) hval hdist (by rw [hlen]; exact hD.1)
  rw [hitems] at ho1 ho2 ho3 ho4
  revert hev
  cases hst : (CardDemo.Cbact04c.model4x (vals3.map acctAcc) (vals2.map CardXrefRecord.encode)
    (vals4.map discOf) (parmOf link1) (sp 76) (sp 20) (fun _ => clk)
    (CardDemo.Cbact04c.items (accsOf vals1 vals2 vals3))).stop with
  | true =>
    intro hev
    simp only [↓reduceIte] at hev
    obtain ⟨hstop, hout⟩ := hev
    rw [hst] at ho1 ho2
    simp only [↓reduceIte, List.append_nil] at ho2
    refine ⟨.inr hstop, ?_, ?_, ?_, ?_⟩
    · rw [ho2]
      simp only [displays, hout, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.filterMap_append, List.map_append]
      simp [dispOf, startMsg_text]
      rfl
    · rw [ho3]
      simp only [writes, hout, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.filterMap_append, List.map_append]
      simp [wrOf]
      rfl
    · rw [ho4]
      simp only [rewrites, hout, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.filterMap_append, List.map_append]
      simp [rwOf]
      rfl
    · rw [ho1, hstop]; rfl
  | false =>
    intro hev
    simp only [Bool.false_eq_true, ↓reduceIte] at hev
    obtain ⟨hstop, hout⟩ := hev
    rw [hst] at ho1 ho2
    simp only [Bool.false_eq_true, ↓reduceIte] at ho2
    refine ⟨.inl hstop, ?_, ?_, ?_, ?_⟩
    · rw [ho2]
      simp only [displays, hout, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.filterMap_append, List.map_append]
      simp [dispOf, startMsg_text, endMsg_text]
      rfl
    · rw [ho3]
      simp only [writes, hout, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.filterMap_append, List.map_append]
      simp [wrOf]
      rfl
    · rw [ho4]
      simp only [rewrites, hout, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.filterMap_append, List.map_append]
      simp [rwOf]
      rfl
    · rw [ho1, hstop]; rfl


end EquivLean.Modernize.Cbact04c.Every.Glue
