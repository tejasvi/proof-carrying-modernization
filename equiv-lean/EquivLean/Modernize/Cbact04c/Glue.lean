import EquivLean.Modernize.Cbact04c.Model

/-!
# CBACT04C: the translations' model and coblean's events

coblean's `cbact04c_events` describes CBACT04C's events as `model4`, a fold over the category
records paired with their accounts (`items accs`, `Acc` = the account's record, its card
cross-reference, its categories). `Model.run` is the fold the translations perform on field
values.

`run_events`: when the category records are those of accounts `accs` that `accOf` builds from
the files (`AccOk`: the lookups succeed and the field values are valid), with distinct ids and
fewer than 999999 records, `Model.run`'s outputs are `model4`'s events:
- the displayed lines are their CP037 texts;
- the transactions and rewritten accounts are their records, decoded.

The proof is a simulation, one record at a time (`step_corr`, from `stageA_corr` (display,
change of account) and `stageB_corr` (interest)). Its invariant is `Corr`:
- the current account was read before any rewrite of it;
- the account table differs from the file only at accounts already left.

COBOL's arithmetic is high-order truncation (`fitDec_eq`: `Int.tmod`) and truncating division
(`divRound_trunc`: `Int.tdiv`).
-/

open Cobol EquivLean.Cobol.Rec EquivLean.Modernize.Cbact04c.Model
open CardDemo.Cbact04c (Acc Cat)

namespace EquivLean.Modernize.Cbact04c.Glue


/-! ## Arithmetic: COBOL's truncation and rounding as `Int.tmod` / `Int.tdiv` -/

theorem tmod_neg_of_neg {v m : Int} (_h : v < 0) : Int.tmod v m = -Int.tmod (-v) m := by
  have := Int.neg_tmod (-v) m
  simp at this
  simp

/-- Decimal high-order truncation keeps the sign: `Int.tmod` by `10 ^ n`. -/
theorem fitDec_eq (n : Nat) (v : Int) : (Sem.fitDec n v).2 = Int.tmod v (10 ^ n) := by
  unfold Sem.fitDec truncDigits
  have e : (((10 ^ n : Nat) : Int)) = (10 : Int) ^ n := by simp
  rw [← e]
  generalize 10 ^ n = M
  split
  · rename_i h
    by_cases h0 : 0 ≤ v
    · rw [Int.tmod_eq_of_lt h0 (by omega)]
    · rw [tmod_neg_of_neg (by omega), Int.tmod_eq_of_lt (by omega) (by omega)]
      omega
  · by_cases h0 : 0 ≤ v
    · simp only [h0, ↓reduceIte, Int.tmod_eq_emod_of_nonneg h0]
    · simp only [h0, ↓reduceIte, tmod_neg_of_neg (show v < 0 by omega),
        Int.tmod_eq_emod_of_nonneg (show 0 ≤ -v by omega)]

/-- `fitNum` of a signed DISPLAY item. -/
theorem fitNum_signed {f : NumFmt} (hu : f.usage = .display) (hs : f.signed = true) (v : Int) :
    (Sem.fitNum {} f v).2 = Int.tmod v (10 ^ f.digits) := by
  have hb : f.fullBinary {} = false := by simp [NumFmt.fullBinary, hu]
  simp only [Sem.fitNum, hs, ↓reduceIte, hb, Bool.false_eq_true]
  exact fitDec_eq _ _

/-- `ROUNDED MODE TRUNCATION` division is `Int.tdiv`. -/
theorem divRound_trunc (n d : Int) : divRound .truncation n d = Int.tdiv n d := by
  unfold divRound
  by_cases h0 : 0 ≤ n
  · simp only [h0, ↓reduceIte, Int.tdiv_eq_ediv_of_nonneg h0]
  · simp only [h0, ↓reduceIte]
    have := Int.neg_tdiv (-n) d
    rw [Int.neg_neg] at this
    rw [this, Int.tdiv_eq_ediv_of_nonneg (show 0 ≤ -n by omega)]



theorem num_of_valid {f : Field} {fmt : NumFmt} (hk : f.desc.kind = .num fmt) {v : FVal}
    (h : f.Valid v) : ∃ n, v = .num n ∧ f.Valid (.num n) := by
  cases v with
  | num n => exact ⟨n, rfl, h⟩
  | str bs => obtain ⟨⟨j, hj⟩, -⟩ := h; rw [hk] at hj; cases hj

theorem str_of_valid {f : Field} {j : Bool} (hk : f.desc.kind = .alnum j) {v : FVal}
    (h : f.Valid v) : ∃ bs, v = .str bs ∧ bs.length = f.desc.len := by
  cases v with
  | num n => obtain ⟨fmt, hf, -⟩ := h; rw [hk] at hf; cases hf
  | str bs => exact ⟨bs, rfl, h.2⟩

/-- A DISPLAY numeric value that a picture holds. -/
theorem holds_display {f : NumFmt} (hu : f.usage = .display) {v : Int} :
    f.Holds {} v ↔ v.natAbs < 10 ^ f.digits ∧ (f.signed = false → 0 ≤ v) := by
  have hb : f.fullBinary {} = false := by simp [NumFmt.fullBinary, hu]
  unfold NumFmt.Holds
  simp [hb]

/-! ## Category records -/

/-- The field values of the category record of account `id` and category `c`. -/
def catVals (id : Int) (c : Cat) : List FVal :=
  [.num id, .str c.ty, .num c.cat, .num c.bal, .str c.filler]

/-- The category of a category record. -/
def catOf (t : List FVal) : Cat := ⟨tType t, tCat t, tBal t, strOf (t.getD 4 default)⟩

theorem catVals_encode (id : Int) (c : Cat) :
    TranCatBalRecord.encode (catVals id c) = Cat.bytes id c := by
  have e : TranCatBalRecord.encode (catVals id c) =
      encodeNum {} CardDemo.Cbact04c.TRANCAT_ACCT_ID.fmt id ++ (c.ty ++
        (encodeNum {} CardDemo.Cbact04c.TRANCAT_CD.fmt c.cat ++
          (encodeNum {} CardDemo.Cbact04c.TRAN_CAT_BAL.fmt c.bal ++ (c.filler ++ [])))) := rfl
  rw [e]
  simp [Cat.bytes, List.append_assoc]

/-- A valid category record is the record of its account and category. -/
theorem catVals_catOf {t : List FVal} (ht : TranCatBalRecord.Valid t) :
    t = catVals (tAcct t) (catOf t) ∧ (catOf t).valid ∧ (tAcct t).natAbs < 100000000000 ∧
      0 ≤ tAcct t := by
  have hl : t.length = 5 := ht.length_eq.symm
  match t, hl, ht with
  | [x0, x1, x2, x3, x4], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 .nil)))) =>
    obtain ⟨a, rfl, ha⟩ := num_of_valid rfl h0
    obtain ⟨ty, rfl, hty⟩ := str_of_valid rfl h1
    obtain ⟨cat, rfl, hcat⟩ := num_of_valid rfl h2
    obtain ⟨bal, rfl, hbal⟩ := num_of_valid rfl h3
    obtain ⟨fl, rfl, hfl⟩ := str_of_valid rfl h4
    obtain ⟨_, hk0, -, -, hh0, -⟩ := ha
    obtain ⟨_, hk2, -, -, hh2, -⟩ := hcat
    obtain ⟨_, hk3, -, -, hh3, -⟩ := hbal
    cases hk0; cases hk2; cases hk3
    rw [holds_display rfl] at hh0 hh2 hh3
    refine ⟨rfl, ⟨hty, hfl, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp_all [catOf, tAcct, tType, tCat, tBal, numOf, strOf]



/-! ## Account records -/

/-- The account of id `id` in coblean's model: the fields of its record (`findAcct`), its
cross-reference record (`findXref`), the categories `cats`. -/
def accOf (xrefs accts : List (List FVal)) (id : Int) (cats : List Cat) : Acc :=
  let A := findAcct accts id
  { id, s := strOf (A.getD 1 default), bal := aBal A,
    mid := encodeNum {} CardDemo.Cbact04c.ACCT_CREDIT_LIMIT.fmt (numOf (A.getD 3 default)) ++
      encodeNum {} CardDemo.Cbact04c.ACCT_CASH_CREDIT_LIMIT.fmt (numOf (A.getD 4 default)) ++
      strOf (A.getD 5 default) ++ strOf (A.getD 6 default) ++ strOf (A.getD 7 default),
    cc := numOf (A.getD 8 default), cd := numOf (A.getD 9 default),
    zip := strOf (A.getD 10 default), grp := aGrp A, af := strOf (A.getD 12 default),
    xrec := CardXrefRecord.encode (findXref xrefs id), cats }

/-- An account record's values, by kind. -/
theorem acct_shape {A : List FVal} (hA : AccountRecord.Valid A) :
    ∃ id s bal cl ccl od ed rd cc cd zip grp af,
      A = [.num id, .str s, .num bal, .num cl, .num ccl, .str od, .str ed, .str rd, .num cc,
        .num cd, .str zip, .str grp, .str af] ∧
      id.natAbs < 100000000000 ∧ 0 ≤ id ∧ s.length = 1 ∧ bal.natAbs < 1000000000000 ∧
      cl.natAbs < 1000000000000 ∧ ccl.natAbs < 1000000000000 ∧ od.length = 10 ∧
      ed.length = 10 ∧ rd.length = 10 ∧ cc.natAbs < 1000000000000 ∧
      cd.natAbs < 1000000000000 ∧ zip.length = 10 ∧ grp.length = 10 ∧ af.length = 178 := by
  have hl : A.length = 13 := hA.length_eq.symm
  match A, hl, hA with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12], _,
      .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8 (.cons h9 (.cons h10 (.cons h11 (.cons h12 .nil)))))))))))) =>
    obtain ⟨id, rfl, hid⟩ := num_of_valid rfl h0
    obtain ⟨s, rfl, hs⟩ := str_of_valid rfl h1
    obtain ⟨bal, rfl, hbal⟩ := num_of_valid rfl h2
    obtain ⟨cl, rfl, hcl⟩ := num_of_valid rfl h3
    obtain ⟨ccl, rfl, hccl⟩ := num_of_valid rfl h4
    obtain ⟨od, rfl, hod⟩ := str_of_valid rfl h5
    obtain ⟨ed, rfl, hed⟩ := str_of_valid rfl h6
    obtain ⟨rd, rfl, hrd⟩ := str_of_valid rfl h7
    obtain ⟨cc, rfl, hcc⟩ := num_of_valid rfl h8
    obtain ⟨cd, rfl, hcd⟩ := num_of_valid rfl h9
    obtain ⟨zip, rfl, hzip⟩ := str_of_valid rfl h10
    obtain ⟨grp, rfl, hgrp⟩ := str_of_valid rfl h11
    obtain ⟨af, rfl, haf⟩ := str_of_valid rfl h12
    obtain ⟨_, k0, -, -, n0, -⟩ := hid
    obtain ⟨_, k2, -, -, n2, -⟩ := hbal
    obtain ⟨_, k3, -, -, n3, -⟩ := hcl
    obtain ⟨_, k4, -, -, n4, -⟩ := hccl
    obtain ⟨_, k8, -, -, n8, -⟩ := hcc
    obtain ⟨_, k9, -, -, n9, -⟩ := hcd
    cases k0; cases k2; cases k3; cases k4; cases k8; cases k9
    rw [holds_display rfl] at n0 n2 n3 n4 n8 n9
    refine ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, ?_⟩
    simp_all

/-- The record of `accOf` is the account's record. -/
theorem accOf_bytes (xrefs accts : List (List FVal)) (id : Int) (cats : List Cat)
    (hA : AccountRecord.Valid (findAcct accts id)) (hid : aId (findAcct accts id) = id) :
    (accOf xrefs accts id cats).bytes = AccountRecord.encode (findAcct accts id) := by
  obtain ⟨i, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, hA', -⟩ := acct_shape hA
  have e : AccountRecord.encode [.num i, .str s, .num bal, .num cl, .num ccl, .str od, .str ed,
      .str rd, .num cc, .num cd, .str zip, .str grp, .str af] =
      encodeNum {} CardDemo.Cbact04c.ACCT_ID.fmt i ++ (s ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CURR_BAL.fmt bal ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CREDIT_LIMIT.fmt cl ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CASH_CREDIT_LIMIT.fmt ccl ++ (od ++ (ed ++ (rd ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CURR_CYC_CREDIT.fmt cc ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CURR_CYC_DEBIT.fmt cd ++
      (zip ++ (grp ++ (af ++ [])))))))))))) := rfl
  rw [hA'] at hid ⊢
  simp only [aId, numOf, List.getD_cons_zero] at hid
  subst hid
  rw [e]
  simp [accOf, Acc.bytes, hA', aBal, aGrp, numOf, strOf, List.append_assoc]

/-- The account record with the interest posted, as coblean's `Acc.posted`. -/
theorem posted_bytes (xrefs accts : List (List FVal)) (id : Int) (cats : List Cat) (t : Int)
    (hA : AccountRecord.Valid (findAcct accts id)) (hid : aId (findAcct accts id) = id) :
    (accOf xrefs accts id cats).posted t = AccountRecord.encode (posted (findAcct accts id) t) ∧
      AccountRecord.Valid (posted (findAcct accts id) t) := by
  obtain ⟨i, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, hA', hi, hi0, hs, hbal, hcl, hccl,
    hod, hed, hrd, hcc, hcd, hzip, hgrp, haf⟩ := acct_shape hA
  rw [hA'] at hid
  simp only [aId, numOf, List.getD_cons_zero] at hid
  subst hid
  have hp : posted (findAcct accts i) t = [.num i, .str s,
      .num (Int.tmod (bal + t) (10 ^ 12)), .num cl, .num ccl, .str od, .str ed, .str rd, .num 0,
      .num 0, .str zip, .str grp, .str af] := by
    rw [hA']; rfl
  have e : AccountRecord.encode [.num i, .str s, .num (Int.tmod (bal + t) (10 ^ 12)), .num cl,
      .num ccl, .str od, .str ed, .str rd, .num 0, .num 0, .str zip, .str grp, .str af] =
      encodeNum {} CardDemo.Cbact04c.ACCT_ID.fmt i ++ (s ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CURR_BAL.fmt (Int.tmod (bal + t) (10 ^ 12)) ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CREDIT_LIMIT.fmt cl ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CASH_CREDIT_LIMIT.fmt ccl ++ (od ++ (ed ++ (rd ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CURR_CYC_CREDIT.fmt 0 ++
      (encodeNum {} CardDemo.Cbact04c.ACCT_CURR_CYC_DEBIT.fmt 0 ++
      (zip ++ (grp ++ (af ++ [])))))))))))) := rfl
  have hfit : (Sem.fitNum {} CardDemo.Cbact04c.ACCT_CURR_BAL.fmt (bal + t)).2 =
      Int.tmod (bal + t) (10 ^ 12) := fitNum_signed rfl rfl _
  refine ⟨?_, ?_⟩
  · rw [hp, e]
    simp [accOf, Acc.posted, hA', aBal, aGrp, numOf, strOf, List.append_assoc, hfit]
  · rw [hp]
    have hb : (Int.tmod (bal + t) (10 ^ 12)).natAbs < 1000000000000 := by
      rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by decide)
    refine .cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hi, fun _ => hi0⟩, rfl⟩
      (.cons ⟨⟨_, rfl⟩, hs⟩ (.cons ⟨_, rfl, by decide, by decide,
        (holds_display rfl).2 ⟨hb, fun h => by cases h⟩, rfl⟩
      (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hcl, fun h => by cases h⟩, rfl⟩
      (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hccl, fun h => by cases h⟩, rfl⟩
      (.cons ⟨⟨_, rfl⟩, hod⟩ (.cons ⟨⟨_, rfl⟩, hed⟩ (.cons ⟨⟨_, rfl⟩, hrd⟩
      (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨by decide, fun h => by cases h⟩, rfl⟩
      (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨by decide, fun h => by cases h⟩, rfl⟩
      (.cons ⟨⟨_, rfl⟩, hzip⟩ (.cons ⟨⟨_, rfl⟩, hgrp⟩ (.cons ⟨⟨_, rfl⟩, haf⟩ .nil))))))))))))

/-! ## Transaction records -/

theorem length_db2ts (c : List UInt8) (h : 16 ≤ c.length) : (CardDemo.Cbact04c.db2ts c).length = 26 := by
  simp [CardDemo.Cbact04c.db2ts, List.length_take, List.length_drop]
  omega

theorem spaces110_eq : CardDemo.Cbact04c.spaces110 = sp 50 ++ (sp 50 ++ sp 10) := by decide

/-- The interest transaction, as coblean's `txRec` (with the harness storage's spaces in the tail
of `TRAN-DESC` and in the `FILLER`). -/
theorem txRec_eq (parm clk card : List UInt8) (k0 : Nat) (a : Acc) (amt : Int)
    (hcard : a.xrec.take 16 = card) :
    CardDemo.Cbact04c.txRec parm (sp 76) (sp 20) (fun _ => clk) k0 a amt =
      TranRecord.encode (tranVals parm clk (k0 + 1) a.id card amt) := by
  have e : TranRecord.encode (tranVals parm clk (k0 + 1) a.id card amt) =
      (parm ++ encodeNum {} CardDemo.Cbact04c.WS_TRANID_SUFFIX.fmt ((k0 + 1 : Nat) : Int)) ++
      ([240, 241] ++ (encodeNum {} CardDemo.Cbact04c.TRAN_CAT_CD.fmt 5 ++
      (CardDemo.Cbact04c.systemSrc ++
      ((CardDemo.Cbact04c.descHead ++ encodeNum {} CardDemo.Cbact04c.ACCT_ID.fmt a.id ++ sp 76) ++
      (encodeNum {} CardDemo.Cbact04c.TRAN_AMT.fmt amt ++
      (encodeNum {} CardDemo.Cbact04c.TRAN_MERCHANT_ID.fmt 0 ++ (sp 50 ++ (sp 50 ++ (sp 10 ++
      (card ++ (CardDemo.Cbact04c.db2ts clk ++ (CardDemo.Cbact04c.db2ts clk ++
      (sp 20 ++ []))))))))))))) := rfl
  rw [e, CardDemo.Cbact04c.txRec, spaces110_eq, hcard]
  simp [List.append_assoc]

/-- The transaction's field values are valid. -/
theorem tranVals_valid (parm clk card : List UInt8) (k : Nat) (id amt : Int)
    (hp : parm.length = 10) (hc : 16 ≤ clk.length) (hcard : card.length = 16)
    (hk : k < 1000000) (hid : id.natAbs < 100000000000) (hamt : amt.natAbs < 100000000000) :
    TranRecord.Valid (tranVals parm clk k id card amt) := by
  have h1 : (encodeNum {} CardDemo.Cbact04c.WS_TRANID_SUFFIX.fmt (k : Int)).length = 6 :=
    length_encodeNum _ _ _ (by decide)
  have h2 : (encodeNum {} CardDemo.Cbact04c.ACCT_ID.fmt id).length = 11 :=
    length_encodeNum _ _ _ (by decide)
  refine .cons ⟨⟨_, rfl⟩, by simp [hp, h1]⟩ (.cons ⟨⟨_, rfl⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨by decide, fun _ => by decide⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, by decide⟩
    (.cons ⟨⟨_, rfl⟩, by simp [h2, sp]; decide⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hamt, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨by decide, fun _ => by decide⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, by simp [sp]⟩ (.cons ⟨⟨_, rfl⟩, by simp [sp]⟩ (.cons ⟨⟨_, rfl⟩, by simp [sp]⟩
    (.cons ⟨⟨_, rfl⟩, hcard⟩
    (.cons ⟨⟨_, rfl⟩, length_db2ts clk hc⟩ (.cons ⟨⟨_, rfl⟩, length_db2ts clk hc⟩
    (.cons ⟨⟨_, rfl⟩, by simp [sp]⟩ .nil)))))))))))))

/-! ## The account table -/

theorem findAcct_replaceFirst (j i : Int) (p : List FVal) (hp : aId p = j) (hij : i ≠ j) :
    ∀ tbl : List (List FVal),
      findAcct (replaceFirst (fun a => aId a == j) p tbl) i = findAcct tbl i
  | [] => rfl
  | y :: ys => by
    have ih := findAcct_replaceFirst j i p hp hij ys
    unfold findAcct at ih ⊢
    simp only [replaceFirst]
    by_cases hy : aId y = j
    · have hji : (j == i) = false := by simp [Ne.symm hij]
      simp [hy, hp, List.find?_cons, hji]
    · have hy' : (aId y == j) = false := by simp [hy]
      simp only [hy', Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      split <;> simp_all

/-! ## The events of coblean's model, as the translations' outputs -/

open CardDemo.Cbact04c (M4 step4 model4 items txRec) in
/-- The lines displayed by the events `l` (oldest first), as code points. -/
def dispOf (l : List Event) : List (List Nat) :=
  (l.filterMap fun | .display bs => some bs | _ => none).map (·.map cp037Code)

/-- The transactions written by the events `l`, decoded. -/
def wrOf (l : List Event) : List (Option (List FVal)) :=
  (l.filterMap fun | .write g bs => if g = 5 then some bs else none | _ => none).map TranRecord.decode

/-- The accounts rewritten by the events `l`, decoded. -/
def rwOf (l : List Event) : List (Option (List FVal)) :=
  (l.filterMap fun | .rewrite g bs => if g = 3 then some bs else none | _ => none).map
    AccountRecord.decode

theorem dispOf_append (l l' : List Event) : dispOf (l ++ l') = dispOf l ++ dispOf l' := by
  simp [dispOf, List.filterMap_append]
theorem wrOf_append (l l' : List Event) : wrOf (l ++ l') = wrOf l ++ wrOf l' := by
  simp [wrOf, List.filterMap_append]
theorem rwOf_append (l l' : List Event) : rwOf (l ++ l') = rwOf l ++ rwOf l' := by
  simp [rwOf, List.filterMap_append]

/-- The translations' state `S` after the same category records as coblean's model state `M`;
`left` = the accounts rewritten so far. -/
structure Corr (xrefs accts : List (List FVal)) (S : St) (M : CardDemo.Cbact04c.M4)
    (left : List Int) : Prop where
  last : S.lastId = M.last.map Acc.id
  total : S.total = M.total
  k : S.k = M.k
  disp : S.disp = txt "START OF EXECUTION OF PROGRAM CBACT04C" :: dispOf M.out.reverse
  wr : S.writes.map some = wrOf M.out.reverse
  rw : S.rewrites.map some = rwOf M.out.reverse
  cur : ∀ l, M.last = some l → S.acct = findAcct accts l.id ∧ S.xref = findXref xrefs l.id ∧
    l = accOf xrefs accts l.id l.cats ∧ l.id ∉ left ∧
    AccountRecord.Valid (findAcct accts l.id) ∧ aId (findAcct accts l.id) = l.id
  tbl : ∀ id, id ∉ left → findAcct S.accts id = findAcct accts id

theorem tcat_display : ∀ f ∈ TranCatBalRecord.fields, DisplayNumeric f := by decide

theorem catVals_valid (id : Int) (c : Cat) (hc : c.valid) (hid : id.natAbs < 100000000000)
    (hid0 : 0 ≤ id) : TranCatBalRecord.Valid (catVals id c) := by
  obtain ⟨hty, hfl, hcat, hcat0, hbal⟩ := hc
  exact .cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hid, fun _ => hid0⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hty⟩ (.cons ⟨_, rfl, by decide, by decide,
      (holds_display rfl).2 ⟨hcat, fun _ => hcat0⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hbal, fun h => by cases h⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hfl⟩ .nil))))

/-- The line a category record displays. -/
theorem catVals_text (id : Int) (c : Cat) (hc : c.valid) (hid : id.natAbs < 100000000000)
    (hid0 : 0 ≤ id) :
    TranCatBalRecord.textS (catVals id c) = (Cat.bytes id c).map cp037Code := by
  rw [Schema.textS_eq tcat_display (catVals_valid id c hc hid hid0), catVals_encode]

theorem decode_posted (xrefs accts : List (List FVal)) (l : Acc) (t : Int)
    (hl : l = accOf xrefs accts l.id l.cats) (hA : AccountRecord.Valid (findAcct accts l.id))
    (hid : aId (findAcct accts l.id) = l.id) :
    AccountRecord.decode (l.posted t) = some (posted (findAcct accts l.id) t) := by
  obtain ⟨e, hv⟩ := posted_bytes xrefs accts l.id l.cats t hA hid
  rw [hl, e]
  have hc : AccountRecord.Contig := by decide
  exact Schema.decode_encode hc hv

theorem decode_txRec (parm clk card : List UInt8) (k0 : Nat) (a : Acc) (amt : Int)
    (hcard : a.xrec.take 16 = card) (hp : parm.length = 10) (hc : 16 ≤ clk.length)
    (hcl : card.length = 16) (hk : k0 + 1 < 1000000) (hid : a.id.natAbs < 100000000000)
    (hamt : amt.natAbs < 100000000000) :
    TranRecord.decode (CardDemo.Cbact04c.txRec parm (sp 76) (sp 20) (fun _ => clk) k0 a amt) =
      some (tranVals parm clk (k0 + 1) a.id card amt) := by
  rw [txRec_eq parm clk card k0 a amt hcard]
  have hco : TranRecord.Contig := by decide
  exact Schema.decode_encode hco (tranVals_valid parm clk card (k0 + 1) a.id amt hp hc hcl hk hid hamt)

theorem monthly_eq (c : Cat) (r : Int) :
    CardDemo.Cbact04c.monthly c r = Int.tmod (Int.tdiv (c.bal * r) 120000) (10 ^ 11) := by
  simp only [CardDemo.Cbact04c.monthly, divRound_trunc]
  exact fitNum_signed rfl rfl _

theorem total_eq (v : Int) :
    (Sem.fitNum {} CardDemo.Cbact04c.WS_TOTAL_INT.fmt v).2 = Int.tmod v (10 ^ 11) :=
  fitNum_signed rfl rfl _

/-- The rate coblean's model uses: the translations' lookup in the disclosure group records. -/
def rateOf (discs : List (List FVal)) (a : Acc) (c : Cat) : Int := findRate discs a.grp c.ty c.cat

/-- The translations' step, in two stages: the display and the change of account, … -/
def stageA (xrefs : List (List FVal)) (s : St) (t : List FVal) : St :=
  let s1 : St := { s with disp := s.disp ++ [TranCatBalRecord.textS t] }
  if s1.lastId = some (tAcct t) then s1
  else
    let p := posted s1.acct s1.total
    let accts := if s1.lastId.isSome then replaceFirst (fun a => aId a == aId s1.acct) p s1.accts
      else s1.accts
    { s1 with accts, rewrites := if s1.lastId.isSome then s1.rewrites ++ [p] else s1.rewrites,
              lastId := some (tAcct t), total := 0, acct := findAcct accts (tAcct t),
              xref := findXref xrefs (tAcct t) }

/-- … then the interest. -/
def stageB (discs : List (List FVal)) (parm clk : List UInt8) (s2 : St) (t : List FVal) : St :=
  let rate := findRate discs (aGrp s2.acct) (tType t) (tCat t)
  if rate = 0 then s2
  else
    let amt := Int.tmod (Int.tdiv (tBal t * rate) 120000) (10 ^ 11)
    let k := (s2.k + 1) % 1000000
    { s2 with total := Int.tmod (s2.total + amt) (10 ^ 11), k,
              writes := s2.writes ++ [tranVals parm clk k (aId s2.acct) (xCard s2.xref) amt] }

theorem step_eq (xrefs discs : List (List FVal)) (parm clk : List UInt8) (s : St) (t : List FVal) :
    Model.step xrefs discs parm clk s t = stageB discs parm clk (stageA xrefs s t) t := rfl

open CardDemo.Cbact04c (M4) in
/-- coblean's `step4`, in the same two stages. -/
def step4A (M : M4) (p : Acc × Cat) : M4 :=
  let out1 := Event.display (Cat.bytes p.1.id p.2) :: M.out
  match M.last with
  | some l => if l.id = p.1.id then { last := some p.1, total := M.total, k := M.k, out := out1 }
    else { last := some p.1, total := 0, k := M.k, out := .rewrite 3 (l.posted M.total) :: out1 }
  | none => { last := some p.1, total := 0, k := M.k, out := out1 }

open CardDemo.Cbact04c (M4) in
def step4B (rate : Acc → Cat → Int) (parm clk : List UInt8) (M : M4) (p : Acc × Cat) : M4 :=
  if rate p.1 p.2 = 0 then M
  else
    let amt := CardDemo.Cbact04c.monthly p.2 (rate p.1 p.2)
    { M with total := (Sem.fitNum {} CardDemo.Cbact04c.WS_TOTAL_INT.fmt (M.total + amt)).2,
             k := M.k + 1,
             out := .write 5 (CardDemo.Cbact04c.txRec parm (sp 76) (sp 20) (fun _ => clk) M.k p.1 amt) ::
               M.out }

theorem step4_eq (rate : Acc → Cat → Int) (parm clk : List UInt8) (M : CardDemo.Cbact04c.M4)
    (p : Acc × Cat) :
    CardDemo.Cbact04c.step4 rate parm (sp 76) (sp 20) (fun _ => clk) M p =
      step4B rate parm clk (step4A M p) p := by
  unfold CardDemo.Cbact04c.step4 step4A step4B
  rcases M.last with _ | l
  · by_cases h : rate p.1 p.2 = 0 <;> simp [h]
  · by_cases hl : l.id = p.1.id <;> by_cases h : rate p.1 p.2 = 0 <;> simp [hl, h]

theorem aId_posted (A : List FVal) (t : Int) : aId (posted A t) = aId A := by
  simp [aId, posted, List.getD_eq_getElem?_getD, List.getElem?_set]

/-- The accounts rewritten after one more record of account `a`. -/
def leftAfter (M : CardDemo.Cbact04c.M4) (a : Acc) (left : List Int) : List Int :=
  match M.last with
  | some l => if l.id = a.id then left else l.id :: left
  | none => left

set_option maxHeartbeats 2000000 in
/-- The display and the change of account keep `Corr`. -/
theorem stageA_corr {xrefs accts : List (List FVal)} {S : St} {M : CardDemo.Cbact04c.M4}
    {left : List Int} {a : Acc} {c : Cat}
    (hC : Corr xrefs accts S M left) (ha : a = accOf xrefs accts a.id a.cats)
    (hfa : AccountRecord.Valid (findAcct accts a.id)) (hfid : aId (findAcct accts a.id) = a.id)
    (hc : c.valid) (hid : a.id.natAbs < 100000000000) (hid0 : 0 ≤ a.id)
    (hfresh : M.last.map Acc.id ≠ some a.id → a.id ∉ left) :
    Corr xrefs accts (stageA xrefs S (catVals a.id c)) (step4A M (a, c)) (leftAfter M a left) := by
  have htext := catVals_text a.id c hc hid hid0
  have ht : tAcct (catVals a.id c) = a.id := rfl
  obtain ⟨hlast, htotal, hk', hdisp, hwr, hrw, hcur, htbl⟩ := hC
  rcases hM : M.last with _ | l
  · have hS : S.lastId = none := by rw [hlast, hM]; rfl
    have hfr : a.id ∉ left := hfresh (by rw [hM]; simp)
    simp only [stageA, step4A, leftAfter, hS, hM, ht, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, reduceCtorEq, htbl a.id hfr]
    refine ⟨rfl, rfl, hk', ?_, ?_, ?_, ?_, htbl⟩
    · simp [hdisp, dispOf_append, dispOf, htext]
    · simp [hwr, wrOf_append, wrOf]
    · simp [hrw, rwOf_append, rwOf]
    · intro l hl
      cases hl
      exact ⟨rfl, rfl, ha, hfr, hfa, hfid⟩
  · obtain ⟨hacc, hxr, hl, hlleft, hlv, hlid⟩ := hcur l hM
    have hS : S.lastId = some l.id := by rw [hlast, hM]; rfl
    by_cases hla : l.id = a.id
    · simp only [stageA, step4A, leftAfter, hS, hM, ht, hla, ↓reduceIte]
      refine ⟨rfl, htotal, hk', ?_, ?_, ?_, ?_, htbl⟩
      · simp [hdisp, dispOf_append, dispOf, htext]
      · simp [hwr, wrOf_append, wrOf]
      · simp [hrw, rwOf_append, rwOf]
      · intro l' hl'
        cases hl'
        exact ⟨by rw [hacc, hla], by rw [hxr, hla], ha, hla ▸ hlleft, hfa, hfid⟩
    · have hfr : a.id ∉ left := hfresh (by rw [hM]; simpa using hla)
      have hne : some l.id ≠ some a.id := by simpa using hla
      have hsa : aId S.acct = l.id := by rw [hacc, hlid]
      have hpa : aId (posted S.acct S.total) = l.id := by
        rw [← hsa, aId_posted]
      have hfind : findAcct (replaceFirst (fun b => aId b == aId S.acct) (posted S.acct S.total)
          S.accts) a.id = findAcct accts a.id := by
        rw [hsa, findAcct_replaceFirst l.id a.id _ hpa (Ne.symm hla), htbl a.id hfr]
      simp only [stageA, step4A, leftAfter, hS, hM, ht, hla, hne, ↓reduceIte, Option.isSome_some,
        hfind]
      refine ⟨rfl, rfl, hk', ?_, ?_, ?_, ?_, ?_⟩
      · simp [hdisp, dispOf_append, dispOf, htext]
      · simp [hwr, wrOf_append, wrOf]
      · simp only [List.reverse_cons, List.append_assoc, rwOf_append, List.map_append, hrw]
        simp [rwOf, decode_posted xrefs accts l M.total hl hlv hlid, hacc, htotal]
      · intro l' hl'
        cases hl'
        refine ⟨rfl, rfl, ha, ?_, hfa, hfid⟩
        simp [hfr, Ne.symm hla]
      · intro id hid'
        simp only [List.mem_cons, not_or] at hid'
        rw [hsa, findAcct_replaceFirst l.id id _ hpa hid'.1, htbl id hid'.2]

set_option maxHeartbeats 2000000 in
/-- The interest keeps `Corr`. -/
theorem stageB_corr {xrefs accts discs : List (List FVal)} {parm clk : List UInt8}
    {S : St} {M : CardDemo.Cbact04c.M4} {left : List Int} {a : Acc} {c : Cat}
    (hC : Corr xrefs accts S M left) (hlast : M.last = some a)
    (hgrp : a.grp = aGrp (findAcct accts a.id)) (hid : a.id.natAbs < 100000000000)
    (hk : M.k + 1 < 1000000) (hparm : parm.length = 10) (hclk : 16 ≤ clk.length)
    (hcard : (xCard (findXref xrefs a.id)).length = 16)
    (hxrec : a.xrec.take 16 = xCard (findXref xrefs a.id)) :
    Corr xrefs accts (stageB discs parm clk S (catVals a.id c))
      (step4B (rateOf discs) parm clk M (a, c)) left := by
  obtain ⟨hl, htotal, hk', hdisp, hwr, hrw, hcur, htbl⟩ := hC
  obtain ⟨hacc, hxr, -, -, -, haid⟩ := hcur a hlast
  have hrate : findRate discs (aGrp S.acct) (tType (catVals a.id c)) (tCat (catVals a.id c)) =
      rateOf discs a c := by
    simp [rateOf, hgrp, hacc, tType, tCat, catVals, strOf, numOf]
  by_cases hr : rateOf discs a c = 0
  · simp only [stageB, step4B, hrate, hr, ↓reduceIte]
    exact ⟨hl, htotal, hk', hdisp, hwr, hrw, hcur, htbl⟩
  · simp only [stageB, step4B, hrate, hr, ↓reduceIte]
    have hkk : (S.k + 1) % 1000000 = M.k + 1 := by rw [hk']; exact Nat.mod_eq_of_lt hk
    have hamt : Int.tmod (Int.tdiv (tBal (catVals a.id c) * rateOf discs a c) 120000) (10 ^ 11) =
        CardDemo.Cbact04c.monthly c (rateOf discs a c) := by rw [monthly_eq]; rfl
    have hamtb : (CardDemo.Cbact04c.monthly c (rateOf discs a c)).natAbs < 100000000000 := by
      rw [monthly_eq, Int.natAbs_tmod]; exact Nat.mod_lt _ (by decide)
    have hsid : aId S.acct = a.id := by rw [hacc, haid]
    refine ⟨hl, ?_, hkk, ?_, ?_, ?_, hcur, htbl⟩
    · rw [hamt, total_eq, htotal]
    · simp [hdisp, dispOf_append, dispOf]
    · rw [hkk, hamt, hsid, hxr]
      simp only [List.map_append, hwr, List.reverse_cons, wrOf_append]
      simp [wrOf, decode_txRec parm clk _ M.k a _ hxrec hparm hclk hcard hk hid hamtb]
    · simp [hrw, rwOf_append, rwOf]

/-- **One category record**: the translations' step and coblean's `step4` keep `Corr`. -/
theorem step_corr {xrefs accts discs : List (List FVal)} {parm clk : List UInt8}
    {S : St} {M : CardDemo.Cbact04c.M4} {left : List Int} {a : Acc} {c : Cat}
    (hC : Corr xrefs accts S M left)
    (ha : a = accOf xrefs accts a.id a.cats)
    (hfa : AccountRecord.Valid (findAcct accts a.id)) (hfid : aId (findAcct accts a.id) = a.id)
    (hc : c.valid) (hid : a.id.natAbs < 100000000000) (hid0 : 0 ≤ a.id)
    (hfresh : M.last.map Acc.id ≠ some a.id → a.id ∉ left)
    (hk : M.k + 1 < 1000000) (hparm : parm.length = 10) (hclk : 16 ≤ clk.length)
    (hcard : (xCard (findXref xrefs a.id)).length = 16)
    (hxrec : a.xrec.take 16 = xCard (findXref xrefs a.id)) :
    Corr xrefs accts (Model.step xrefs discs parm clk S (catVals a.id c))
      (CardDemo.Cbact04c.step4 (rateOf discs) parm (sp 76) (sp 20) (fun _ => clk) M (a, c))
      (leftAfter M a left) := by
  rw [step_eq, step4_eq]
  have hA := stageA_corr hC ha hfa hfid hc hid hid0 hfresh
  have hgrp : a.grp = aGrp (findAcct accts a.id) := by rw [ha]; rfl
  have hl : (step4A M (a, c)).last = some a := by
    unfold step4A; rcases M.last with _ | l
    · rfl
    · by_cases h : l.id = a.id <;> simp [h]
  have hk2 : (step4A M (a, c)).k = M.k := by
    unfold step4A; rcases M.last with _ | l
    · rfl
    · by_cases h : l.id = a.id <;> simp [h]
  exact stageB_corr hA hl hgrp hid (by rw [hk2]; exact hk) hparm hclk hcard hxrec

theorem step4_k_le (rate : Acc → Cat → Int) (parm clk : List UInt8) (M : CardDemo.Cbact04c.M4)
    (p : Acc × Cat) :
    (CardDemo.Cbact04c.step4 rate parm (sp 76) (sp 20) (fun _ => clk) M p).k ≤ M.k + 1 := by
  rw [step4_eq]
  have hk : (step4A M p).k = M.k := by
    unfold step4A; rcases M.last with _ | l
    · rfl
    · by_cases h : l.id = p.1.id <;> simp [h]
  unfold step4B
  by_cases h : rate p.1 p.2 = 0 <;> simp [h, hk]

/-- What every account of the input satisfies (built by `accOf`; lookups succeed). -/
structure AccOk (xrefs accts : List (List FVal)) (a : Acc) : Prop where
  eq : a = accOf xrefs accts a.id a.cats
  valid : AccountRecord.Valid (findAcct accts a.id)
  found : aId (findAcct accts a.id) = a.id
  idb : a.id.natAbs < 100000000000
  id0 : 0 ≤ a.id
  cats : ∀ c ∈ a.cats, c.valid
  ne : a.cats ≠ []
  card : (xCard (findXref xrefs a.id)).length = 16
  xrec : a.xrec.take 16 = xCard (findXref xrefs a.id)

/-- The records of one account. -/
theorem cats_corr {xrefs accts discs : List (List FVal)} {parm clk : List UInt8} {a : Acc}
    (ha : AccOk xrefs accts a) (hparm : parm.length = 10) (hclk : 16 ≤ clk.length) :
    ∀ (cs : List Cat) (S : St) (M : CardDemo.Cbact04c.M4) (left : List Int),
      (∀ c ∈ cs, c.valid) → Corr xrefs accts S M left →
      (M.last.map Acc.id ≠ some a.id → a.id ∉ left) → M.k + cs.length < 999999 →
      ∃ left', Corr xrefs accts (cs.foldl (fun s c => Model.step xrefs discs parm clk s (catVals a.id c)) S)
          (cs.foldl (fun m c => CardDemo.Cbact04c.step4 (rateOf discs) parm (sp 76) (sp 20)
            (fun _ => clk) m (a, c)) M) left' ∧
        (cs ≠ [] → (cs.foldl (fun m c => CardDemo.Cbact04c.step4 (rateOf discs) parm (sp 76) (sp 20)
            (fun _ => clk) m (a, c)) M).last = some a) ∧
        (cs.foldl (fun m c => CardDemo.Cbact04c.step4 (rateOf discs) parm (sp 76) (sp 20)
            (fun _ => clk) m (a, c)) M).k ≤ M.k + cs.length ∧
        (∀ x ∈ left', x ∈ left ∨ M.last.map Acc.id = some x ∨ x = a.id)
  | [], S, M, left, _, hC, _, _ => ⟨left, hC, fun h => absurd rfl h, by simp, fun x hx => .inl hx⟩
  | c :: cs, S, M, left, hcs, hC, hfresh, hk => by
    have h1 := step_corr (discs := discs) (parm := parm) (clk := clk) hC ha.eq ha.valid ha.found
      (hcs c (by simp)) ha.idb ha.id0 hfresh (by simp at hk; omega) hparm hclk ha.card ha.xrec
    have hl1 : (CardDemo.Cbact04c.step4 (rateOf discs) parm (sp 76) (sp 20) (fun _ => clk) M
        (a, c)).last = some a := by
      rw [step4_eq]; unfold step4B
      have : (step4A M (a, c)).last = some a := by
        unfold step4A; rcases M.last with _ | l
        · rfl
        · by_cases h : l.id = a.id <;> simp [h]
      by_cases h : rateOf discs a c = 0 <;> simp [h, this]
    have hk1 := step4_k_le (rateOf discs) parm clk M (a, c)
    obtain ⟨left', hC', -, hk', hsub⟩ := cats_corr ha hparm hclk cs _ _ _
      (fun c' hc' => hcs c' (by simp [hc'])) h1 (by rw [hl1]; simp)
      (by simp at hk; omega)
    refine ⟨left', hC', fun _ => ?_, ?_, ?_⟩
    · cases cs with
      | nil => simpa using hl1
      | cons c' cs' =>
        obtain ⟨_, -, h, -, -⟩ := cats_corr (discs := discs) ha hparm hclk (c' :: cs') _ _ _
          (fun c'' hc'' => hcs c'' (by simp [hc''])) h1 (by rw [hl1]; simp)
          (by simp at hk ⊢; omega)
        simpa using h (by simp)
    · simp only [List.foldl_cons, List.length_cons]; omega
    · intro x hx
      rcases hsub x hx with h | h | h
      · unfold leftAfter at h
        rcases hM : M.last with _ | l
        · rw [hM] at h; exact .inl h
        · rw [hM] at h
          by_cases hla : l.id = a.id
          · simp only [hla, ↓reduceIte] at h; exact .inl h
          · simp only [hla, ↓reduceIte, List.mem_cons] at h
            rcases h with rfl | h
            · exact .inr (.inl (by simp))
            · exact .inl h
      · rw [hl1] at h; simp at h; exact .inr (.inr h.symm)
      · exact .inr (.inr h)

/-- The records of the accounts `rest`, from a state that has seen none of them. -/
theorem accs_corr {xrefs accts discs : List (List FVal)} {parm clk : List UInt8}
    (hparm : parm.length = 10) (hclk : 16 ≤ clk.length) :
    ∀ (rest : List Acc) (S : St) (M : CardDemo.Cbact04c.M4) (left : List Int),
      Corr xrefs accts S M left →
      (∀ b ∈ rest, b.id ∉ left ∧ M.last.map Acc.id ≠ some b.id) →
      rest.Pairwise (fun a b => a.id ≠ b.id) → (∀ b ∈ rest, AccOk xrefs accts b) →
      M.k + (CardDemo.Cbact04c.items rest).length < 999999 →
      ∃ left', Corr xrefs accts
        ((CardDemo.Cbact04c.items rest).foldl
          (fun s p => Model.step xrefs discs parm clk s (catVals p.1.id p.2)) S)
        ((CardDemo.Cbact04c.items rest).foldl
          (CardDemo.Cbact04c.step4 (rateOf discs) parm (sp 76) (sp 20) (fun _ => clk)) M) left'
  | [], S, M, left, hC, _, _, _, _ => ⟨left, hC⟩
  | a :: rest, S, M, left, hC, hfr, hpw, hok, hk => by
    have ha := hok a (by simp)
    simp only [CardDemo.Cbact04c.items, List.flatMap_cons, List.foldl_append] at hk ⊢
    rw [List.length_append] at hk
    simp only [List.foldl_map]
    obtain ⟨left', hC', hlast, hk', hsub⟩ := cats_corr (discs := discs) ha hparm hclk a.cats S M left
      ha.cats hC (fun _ => (hfr a (by simp)).1) (by simp at hk; omega)
    have hpw' := List.pairwise_cons.1 hpw
    exact accs_corr hparm hclk rest _ _ left' hC'
      (fun b hb => by
        obtain ⟨hbl, hbm⟩ := hfr b (by simp [hb])
        have hab : a.id ≠ b.id := hpw'.1 b hb
        refine ⟨fun hx => ?_, by rw [hlast ha.ne]; simpa using hab⟩
        rcases hsub b.id hx with h | h | h
        · exact hbl h
        · exact hbm h
        · exact hab h.symm)
      hpw'.2 (fun b hb => hok b (by simp [hb]))
      (by simp only [List.length_map] at hk; simp only [CardDemo.Cbact04c.items]; omega)

/-- **The translations' outputs are coblean's events**, for the category records of accounts
`accs` that satisfy `AccOk`, with distinct ids, fewer than 999999 records. -/
theorem run_events {xrefs accts discs : List (List FVal)} {parm clk : List UInt8}
    (hparm : parm.length = 10) (hclk : 16 ≤ clk.length) (accs : List Acc)
    (hok : ∀ a ∈ accs, AccOk xrefs accts a) (hd : accs.Pairwise (fun a b => a.id ≠ b.id))
    (hn : (CardDemo.Cbact04c.items accs).length < 999999) :
    let o := Model.run ((CardDemo.Cbact04c.items accs).map (fun p => catVals p.1.id p.2)) xrefs
      accts discs parm clk
    let M := CardDemo.Cbact04c.model4 (rateOf discs) parm (sp 76) (sp 20) (fun _ => clk)
      (CardDemo.Cbact04c.items accs)
    o.disp = txt "START OF EXECUTION OF PROGRAM CBACT04C" :: dispOf M.out.reverse ++
        [txt "END OF EXECUTION OF PROGRAM CBACT04C"] ∧
      o.writes.map some = wrOf M.out.reverse ∧ o.rewrites.map some = rwOf M.out.reverse := by
  intro o M
  have h0 : Corr xrefs accts (init accts) ⟨none, 0, 0, []⟩ [] :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, (fun l h => by cases h), fun _ _ => rfl⟩
  obtain ⟨left', hC⟩ := accs_corr (discs := discs) hparm hclk accs _ _ [] h0
    (fun b _ => ⟨by simp, by simp⟩) hd hok (by simpa using hn)
  simp only [o, M, Model.run, CardDemo.Cbact04c.model4, List.foldl_map]
  exact ⟨by rw [hC.disp], hC.wr, hC.rw⟩

end EquivLean.Modernize.Cbact04c.Glue
