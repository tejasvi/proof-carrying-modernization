import EquivLean.Modernize.Cbtrn02c.Model
import EquivLean.Modernize.Cbtrn02c.Domain
import EquivLean.Modernize.Cbact04c.Accs

/-!
# CBTRN02C: coblean's model and the translations' model

coblean's `cbtrn02c_posts` describes the COBOL run of CBTRN02C for every input given as coblean's
structures (`Tran`, `Xref`, `Acct`, `TCat`), by its model `model`: a fold over the daily
transactions (`step`, `Model.reject`, `Model.post`).  `Model.run` is the fold the translations
perform on field values.

* `tranOf`, `xrefOf`, `acctOf`, `tcatOf` build coblean's structures from the field values of the
  statements' records: valid structures (`_valid`) with the records' bytes (`_bytes`).
* The proof is a simulation, one daily transaction at a time (`step_corr`, from `reject_corr` and
  `post_corr`).  Its invariant is `Corr`:
  - the account files are equal: coblean's REWRITE at the index of its keyed READ is the
    translations' `replaceFirst` (`replaceFirst_eq_set`);
  - the category balance files give the same first record for every key: the translations append
    a new record, coblean inserts it in key order (`insertCat`), and a record is created only for
    a key that is absent (`find?_insertCat_same`, `find?_insertCat_other`);
  - the `FILLER` of `TRAN-CAT-BAL-RECORD` and the number of rejects are equal, and the outputs are
    those of coblean's events: the lines displayed, the records written and rewritten per file.
* coblean's keyed READs find the translations' first matches (`findKey_some`, `findKey_none`):
  the keys of valid field values are equal exactly when the fields are (`catKeyB_inj`,
  `encodeNum_beq`).
* `cobol_outputs`: with coblean's theorem, the COBOL run of the statements ends with GOBACK, and
  its displays, writes, rewrites and RETURN-CODE are `Model.run`'s.  The harness storage holds
  spaces in the `FILLER`s of WORKING-STORAGE's `TRAN-RECORD` and `TRAN-CAT-BAL-RECORD`
  (`initMem_tfill`, `initMem_catFill`), as `Model.run` has it.

The proofs about the COBOL run never introduce the run as a local definition (`intro` of a `let`
of the statement): the kernel would compare the local definition with the run term by evaluating
coblean's interpreter (about 40 s per comparison).
-/

open Cobol EquivLean.Cobol.Rec EquivLean.Modernize.Cbtrn02c.Model
open CardDemo.Cbtrn02c (Tran Xref Acct TCat)
open EquivLean.Modernize.Cbact04c.Glue (num_of_valid str_of_valid holds_display fitNum_signed)

namespace EquivLean.Modernize.Cbtrn02c.Glue

/-! ## The input records as coblean's structures -/

/-- coblean's daily transaction of a record's field values. -/
def tranOf (t : List FVal) : Tran :=
  ⟨tId t, tType t, tCat t, strOf (t.getD 3 default), strOf (t.getD 4 default), tAmt t,
    numOf (t.getD 6 default), strOf (t.getD 7 default), strOf (t.getD 8 default),
    strOf (t.getD 9 default), tCard t, tOrig t, strOf (t.getD 12 default),
    strOf (t.getD 13 default)⟩

/-- coblean's card cross-reference of a record's field values (the customer id as its bytes). -/
def xrefOf (x : List FVal) : Xref :=
  ⟨xCard x, encodeNum {} CardDemo.Cbtrn02c.XREF_CUST_ID.fmt (numOf (x.getD 1 default)), xAcct x,
    strOf (x.getD 3 default)⟩

/-- coblean's account of a record's field values (the fields the program does not read as
bytes). -/
def acctOf (a : List FVal) : Acct :=
  ⟨encodeNum {} CardDemo.Cbtrn02c.ACCT_ID.fmt (aId a), strOf (a.getD 1 default), aBal a, aLimit a,
    encodeNum {} CardDemo.Cbtrn02c.ACCT_CASH_CREDIT_LIMIT.fmt (numOf (a.getD 4 default)) ++
      strOf (a.getD 5 default),
    aExp a, strOf (a.getD 7 default), aCC a, aCD a,
    strOf (a.getD 10 default) ++ strOf (a.getD 11 default) ++ strOf (a.getD 12 default)⟩

/-- The key of a category balance record (`FD-TRAN-CAT-KEY`): account id, type, category. -/
def catKeyB (acct : Int) (ty : List UInt8) (cd : Int) : List UInt8 :=
  encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt acct ++ ty ++
    encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt cd

/-- coblean's category balance record of a record's field values. -/
def tcatOf (c : List FVal) : TCat := ⟨catKeyB (cAcct c) (cType c) (cCd c), cBal c, cFill c⟩

theorem tran_shape {t : List FVal} (ht : DalytranRecord.Valid t) :
    ∃ id ty cat src desc amt merch mname mcity mzip card orig proc fill,
      t = [.str id, .str ty, .num cat, .str src, .str desc, .num amt, .num merch, .str mname,
        .str mcity, .str mzip, .str card, .str orig, .str proc, .str fill] ∧
      (tranOf t).valid := by
  have hl : t.length = 14 := ht.length_eq.symm
  match t, hl, ht with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13], _,
      .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8
        (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 .nil))))))))))))) =>
    obtain ⟨id, rfl, hid⟩ := str_of_valid rfl h0
    obtain ⟨ty, rfl, hty⟩ := str_of_valid rfl h1
    obtain ⟨cat, rfl, hcat⟩ := num_of_valid rfl h2
    obtain ⟨src, rfl, hsrc⟩ := str_of_valid rfl h3
    obtain ⟨desc, rfl, hdesc⟩ := str_of_valid rfl h4
    obtain ⟨amt, rfl, hamt⟩ := num_of_valid rfl h5
    obtain ⟨merch, rfl, hmerch⟩ := num_of_valid rfl h6
    obtain ⟨mname, rfl, hmname⟩ := str_of_valid rfl h7
    obtain ⟨mcity, rfl, hmcity⟩ := str_of_valid rfl h8
    obtain ⟨mzip, rfl, hmzip⟩ := str_of_valid rfl h9
    obtain ⟨card, rfl, hcard⟩ := str_of_valid rfl h10
    obtain ⟨orig, rfl, horig⟩ := str_of_valid rfl h11
    obtain ⟨proc, rfl, hproc⟩ := str_of_valid rfl h12
    obtain ⟨fill, rfl, hfill⟩ := str_of_valid rfl h13
    obtain ⟨_, k2, -, -, n2, -⟩ := hcat
    obtain ⟨_, k5, -, -, n5, -⟩ := hamt
    obtain ⟨_, k6, -, -, n6, -⟩ := hmerch
    cases k2; cases k5; cases k6
    rw [holds_display rfl] at n2 n5 n6
    refine ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, ?_⟩
    simp_all [tranOf, Tran.valid, tId, tType, tCat, tAmt, tCard, tOrig, strOf, numOf]

theorem tranOf_valid {t : List FVal} (ht : DalytranRecord.Valid t) : (tranOf t).valid := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := tran_shape ht
  exact h

theorem tranOf_bytes {t : List FVal} (ht : DalytranRecord.Valid t) :
    (tranOf t).bytes = DalytranRecord.encode t := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, -⟩ :=
    tran_shape ht
  have e : DalytranRecord.encode [.str id, .str ty, .num cat, .str src, .str desc, .num amt,
      .num merch, .str mname, .str mcity, .str mzip, .str card, .str orig, .str proc, .str fill] =
      id ++ (ty ++ (encodeNum {} CardDemo.Cbtrn02c.DALYTRAN_CAT_CD.fmt cat ++ (src ++ (desc ++
      (encodeNum {} CardDemo.Cbtrn02c.DALYTRAN_AMT.fmt amt ++
      (encodeNum {} CardDemo.Cbtrn02c.DALYTRAN_MERCHANT_ID.fmt merch ++ (mname ++ (mcity ++
      (mzip ++ (card ++ (orig ++ (proc ++ (fill ++ []))))))))))))) := rfl
  rw [e]
  simp [Tran.bytes, tranOf, tId, tType, tCat, tAmt, tCard, tOrig, strOf, numOf, List.append_assoc]

theorem xref_shape {x : List FVal} (hx : CardXrefRecord.Valid x) :
    ∃ card cust acct fill, x = [.str card, .num cust, .num acct, .str fill] ∧
      card.length = 16 ∧ cust.natAbs < 1000000000 ∧ 0 ≤ cust ∧ acct.natAbs < 100000000000 ∧
      0 ≤ acct ∧ fill.length = 14 := by
  have hl : x.length = 4 := hx.length_eq.symm
  match x, hl, hx with
  | [x0, x1, x2, x3], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))) =>
    obtain ⟨card, rfl, hcard⟩ := str_of_valid rfl h0
    obtain ⟨cust, rfl, hcust⟩ := num_of_valid rfl h1
    obtain ⟨acct, rfl, hacct⟩ := num_of_valid rfl h2
    obtain ⟨fill, rfl, hfill⟩ := str_of_valid rfl h3
    obtain ⟨_, k1, -, -, n1, -⟩ := hcust
    obtain ⟨_, k2, -, -, n2, -⟩ := hacct
    cases k1; cases k2
    rw [holds_display rfl] at n1 n2
    refine ⟨card, cust, acct, fill, rfl, ?_⟩
    simp_all

theorem xrefOf_valid {x : List FVal} (hx : CardXrefRecord.Valid x) : (xrefOf x).valid := by
  obtain ⟨card, cust, acct, fill, rfl, h1, -, -, h4, h5, h6⟩ := xref_shape hx
  have hc : (encodeNum {} CardDemo.Cbtrn02c.XREF_CUST_ID.fmt cust).length = 9 :=
    (length_encodeNum {} CardDemo.Cbtrn02c.XREF_CUST_ID.fmt _ (by decide)).trans rfl
  exact ⟨h1, hc, h4, h5, h6⟩

theorem xrefOf_bytes {x : List FVal} (hx : CardXrefRecord.Valid x) :
    (xrefOf x).bytes = CardXrefRecord.encode x := by
  obtain ⟨card, cust, acct, fill, rfl, -⟩ := xref_shape hx
  have e : CardXrefRecord.encode [.str card, .num cust, .num acct, .str fill] =
      card ++ (encodeNum {} CardDemo.Cbtrn02c.XREF_CUST_ID.fmt cust ++
        (encodeNum {} CardDemo.Cbtrn02c.XREF_ACCT_ID.fmt acct ++ (fill ++ []))) := rfl
  rw [e]
  simp [Xref.bytes, xrefOf, xCard, xAcct, strOf, numOf, List.append_assoc]

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
      .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8
        (.cons h9 (.cons h10 (.cons h11 (.cons h12 .nil)))))))))))) =>
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

theorem acctOf_valid {A : List FVal} (hA : AccountRecord.Valid A) : (acctOf A).valid := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, hid, -, hs, hbal, hcl, -,
    hod, hed, hrd, hcc, hcd, hzip, hgrp, haf⟩ := acct_shape hA
  have hi : (encodeNum {} CardDemo.Cbtrn02c.ACCT_ID.fmt id).length = 11 :=
    (length_encodeNum {} CardDemo.Cbtrn02c.ACCT_ID.fmt _ (by decide)).trans rfl
  refine ⟨hi, hs, hbal, hcl, ?_, hed, hrd, hcc, hcd, ?_⟩
  · simp [acctOf, strOf, hod,
      length_encodeNum {} CardDemo.Cbtrn02c.ACCT_CASH_CREDIT_LIMIT.fmt _ (by decide)]
    rfl
  · simp [acctOf, strOf, hzip, hgrp, haf]

theorem acctOf_bytes {A : List FVal} (hA : AccountRecord.Valid A) :
    (acctOf A).bytes = AccountRecord.encode A := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, -⟩ := acct_shape hA
  have e : AccountRecord.encode [.num id, .str s, .num bal, .num cl, .num ccl, .str od, .str ed,
      .str rd, .num cc, .num cd, .str zip, .str grp, .str af] =
      encodeNum {} CardDemo.Cbtrn02c.ACCT_ID.fmt id ++ (s ++
      (encodeNum {} CardDemo.Cbtrn02c.ACCT_CURR_BAL.fmt bal ++
      (encodeNum {} CardDemo.Cbtrn02c.ACCT_CREDIT_LIMIT.fmt cl ++
      (encodeNum {} CardDemo.Cbtrn02c.ACCT_CASH_CREDIT_LIMIT.fmt ccl ++ (od ++ (ed ++ (rd ++
      (encodeNum {} CardDemo.Cbtrn02c.ACCT_CURR_CYC_CREDIT.fmt cc ++
      (encodeNum {} CardDemo.Cbtrn02c.ACCT_CURR_CYC_DEBIT.fmt cd ++
      (zip ++ (grp ++ (af ++ [])))))))))))) := rfl
  rw [e]
  simp [Acct.bytes, acctOf, aId, aBal, aLimit, aExp, aCC, aCD, strOf, numOf, List.append_assoc]

theorem tcat_shape {c : List FVal} (hc : TranCatBalRecord.Valid c) :
    ∃ acct ty cd bal fill, c = [.num acct, .str ty, .num cd, .num bal, .str fill] ∧
      acct.natAbs < 100000000000 ∧ 0 ≤ acct ∧ ty.length = 2 ∧ cd.natAbs < 10000 ∧ 0 ≤ cd ∧
      bal.natAbs < 100000000000 ∧ fill.length = 22 := by
  have hl : c.length = 5 := hc.length_eq.symm
  match c, hl, hc with
  | [x0, x1, x2, x3, x4], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 .nil)))) =>
    obtain ⟨acct, rfl, hacct⟩ := num_of_valid rfl h0
    obtain ⟨ty, rfl, hty⟩ := str_of_valid rfl h1
    obtain ⟨cd, rfl, hcd⟩ := num_of_valid rfl h2
    obtain ⟨bal, rfl, hbal⟩ := num_of_valid rfl h3
    obtain ⟨fill, rfl, hfill⟩ := str_of_valid rfl h4
    obtain ⟨_, k0, -, -, n0, -⟩ := hacct
    obtain ⟨_, k2, -, -, n2, -⟩ := hcd
    obtain ⟨_, k3, -, -, n3, -⟩ := hbal
    cases k0; cases k2; cases k3
    rw [holds_display rfl] at n0 n2 n3
    refine ⟨acct, ty, cd, bal, fill, rfl, ?_⟩
    simp_all

theorem catKeyB_length (acct : Int) (ty : List UInt8) (cd : Int) (hty : ty.length = 2) :
    (catKeyB acct ty cd).length = 17 := by
  simp [catKeyB, hty, length_encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt _ (by decide),
    length_encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt _ (by decide)]
  rfl

theorem tcatOf_valid {c : List FVal} (hc : TranCatBalRecord.Valid c) : (tcatOf c).valid := by
  obtain ⟨acct, ty, cd, bal, fill, rfl, -, -, hty, -, -, hbal, hfill⟩ := tcat_shape hc
  exact ⟨catKeyB_length _ _ _ hty, hbal, hfill⟩

theorem tcatOf_bytes {c : List FVal} (hc : TranCatBalRecord.Valid c) :
    (tcatOf c).bytes = TranCatBalRecord.encode c := by
  obtain ⟨acct, ty, cd, bal, fill, rfl, -⟩ := tcat_shape hc
  have e : TranCatBalRecord.encode [.num acct, .str ty, .num cd, .num bal, .str fill] =
      encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt acct ++ (ty ++
      (encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt cd ++
      (encodeNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt bal ++ (fill ++ [])))) := rfl
  rw [e]
  simp [TCat.bytes, tcatOf, catKeyB, cAcct, cType, cCd, cBal, cFill, strOf, numOf,
    List.append_assoc]

/-! ## The records written -/

theorem length_db2ts (c : List UInt8) (h : 16 ≤ c.length) :
    (CardDemo.Cbtrn02c.db2ts c).length = 26 := by
  simp [CardDemo.Cbtrn02c.db2ts, List.length_take, List.length_drop]
  omega

/-- The transaction record of a posted transaction is coblean's `tranRec` (with the harness
storage's spaces in the `FILLER`). -/
theorem tranVals_encode {t : List FVal} (ht : DalytranRecord.Valid t) (clk : List UInt8) :
    TranRecord.encode (tranVals t clk) =
      CardDemo.Cbtrn02c.tranRec (tranOf t) (CardDemo.Cbtrn02c.db2ts clk) (sp 20) := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, -⟩ :=
    tran_shape ht
  have e : TranRecord.encode (tranVals [.str id, .str ty, .num cat, .str src, .str desc, .num amt,
      .num merch, .str mname, .str mcity, .str mzip, .str card, .str orig, .str proc, .str fill]
      clk) =
      id ++ (ty ++ (encodeNum {} CardDemo.Cbtrn02c.TRAN_CAT_CD.fmt cat ++ (src ++ (desc ++
      (encodeNum {} CardDemo.Cbtrn02c.TRAN_AMT.fmt amt ++
      (encodeNum {} CardDemo.Cbtrn02c.TRAN_MERCHANT_ID.fmt merch ++ (mname ++ (mcity ++
      (mzip ++ (card ++ (orig ++ (CardDemo.Cbtrn02c.db2ts clk ++ (sp 20 ++ []))))))))))))) := rfl
  rw [e]
  simp [CardDemo.Cbtrn02c.tranRec, tranOf, tId, tType, tCat, tAmt, tCard, tOrig, strOf, numOf,
    List.append_assoc]

theorem tranVals_valid {t : List FVal} (ht : DalytranRecord.Valid t) {clk : List UInt8}
    (hclk : 16 ≤ clk.length) : TranRecord.Valid (tranVals t clk) := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl,
    hid, hty, hcat, hcat0, hsrc, hdesc, hamt, hmerch, hmerch0, hmname, hmcity, hmzip, hcard, horig,
    -, -⟩ := tran_shape ht
  exact .cons ⟨⟨_, rfl⟩, hid⟩ (.cons ⟨⟨_, rfl⟩, hty⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hcat, fun _ => hcat0⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hsrc⟩ (.cons ⟨⟨_, rfl⟩, hdesc⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hamt, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hmerch, fun _ => hmerch0⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hmname⟩ (.cons ⟨⟨_, rfl⟩, hmcity⟩ (.cons ⟨⟨_, rfl⟩, hmzip⟩
    (.cons ⟨⟨_, rfl⟩, hcard⟩ (.cons ⟨⟨_, rfl⟩, horig⟩
    (.cons ⟨⟨_, rfl⟩, length_db2ts clk hclk⟩ (.cons ⟨⟨_, rfl⟩, by simp [sp]⟩ .nil)))))))))))))

theorem decode_tranRec {t : List FVal} (ht : DalytranRecord.Valid t) {clk : List UInt8}
    (hclk : 16 ≤ clk.length) :
    TranRecord.decode (CardDemo.Cbtrn02c.tranRec (tranOf t) (CardDemo.Cbtrn02c.db2ts clk) (sp 20)) =
      some (tranVals t clk) := by
  rw [← tranVals_encode ht clk]
  exact Schema.decode_encode (by decide) (tranVals_valid ht hclk)

theorem trailer_length (code : Int) {desc : List UInt8} (h : desc.length ≤ 76) :
    (CardDemo.Cbtrn02c.trailer code desc).length = 80 := by
  simp [CardDemo.Cbtrn02c.trailer,
    length_encodeNum {} CardDemo.Cbtrn02c.WS_VALIDATION_FAIL_REASON.fmt _ (by decide)]
  change 4 + (desc.length + (76 - desc.length)) = 80
  omega

/-- A rejected transaction's record is coblean's (the daily record, then the trailer). -/
theorem decode_reject {t : List FVal} (ht : DalytranRecord.Valid t) (code : Int)
    {desc : List UInt8} (hd : desc.length ≤ 76) :
    RejectRecord.decode ((tranOf t).bytes ++ CardDemo.Cbtrn02c.trailer code desc) =
      some (rejectVals t code desc) := by
  have e : RejectRecord.encode (rejectVals t code desc) =
      DalytranRecord.encode t ++ (CardDemo.Cbtrn02c.trailer code desc ++ []) := rfl
  have hl : (DalytranRecord.encode t).length = 350 := Schema.length_encode (by decide) ht
  rw [tranOf_bytes ht, ← List.append_nil (CardDemo.Cbtrn02c.trailer code desc), ← e]
  exact Schema.decode_encode (by decide)
    (.cons ⟨⟨_, rfl⟩, hl⟩ (.cons ⟨⟨_, rfl⟩, trailer_length code hd⟩ .nil))

/-- coblean's account after the posting (`2800-UPDATE-ACCOUNT-REC`) is that of `postAcct`. -/
theorem acctOf_post {A : List FVal} (hA : AccountRecord.Valid A) (amt : Int) :
    acctOf (postAcct A amt) = { acctOf A with
      bal := (Sem.fitNum {} CardDemo.Cbtrn02c.ACCT_CURR_BAL.fmt ((acctOf A).bal + amt)).2,
      cc := if 0 ≤ amt then (Sem.fitNum {} CardDemo.Cbtrn02c.ACCT_CURR_CYC_CREDIT.fmt
        ((acctOf A).cc + amt)).2 else (acctOf A).cc,
      cd := if 0 ≤ amt then (acctOf A).cd
        else (Sem.fitNum {} CardDemo.Cbtrn02c.ACCT_CURR_CYC_DEBIT.fmt ((acctOf A).cd + amt)).2 } := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, -⟩ := acct_shape hA
  by_cases h : 0 ≤ amt <;>
    simp [postAcct, acctOf, h, aId, aBal, aLimit, aExp, aCC, aCD, strOf, numOf]

theorem postAcct_valid {A : List FVal} (hA : AccountRecord.Valid A) (amt : Int) :
    AccountRecord.Valid (postAcct A amt) := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, hid, hid0, hs, hbal, hcl,
    hccl, hod, hed, hrd, hcc, hcd, hzip, hgrp, haf⟩ := acct_shape hA
  have hb := CardDemo.Cbtrn02c.fitNum_bal (bal + amt)
  have hcc' : (if 0 ≤ amt then (Sem.fitNum {} CardDemo.Cbtrn02c.ACCT_CURR_CYC_CREDIT.fmt
      (cc + amt)).2 else cc).natAbs < 1000000000000 := by
    split
    · exact CardDemo.Cbtrn02c.fitNum_bal _
    · exact hcc
  have hcd' : (if 0 ≤ amt then cd else (Sem.fitNum {} CardDemo.Cbtrn02c.ACCT_CURR_CYC_DEBIT.fmt
      (cd + amt)).2).natAbs < 1000000000000 := by
    split
    · exact hcd
    · exact CardDemo.Cbtrn02c.fitNum_bal _
  simp only [postAcct, aBal, aCC, aCD, numOf, List.getD_cons_succ, List.getD_cons_zero,
    List.set_cons_succ, List.set_cons_zero]
  exact .cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hid, fun _ => hid0⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hs⟩ (.cons ⟨_, rfl, by decide, by decide,
      (holds_display rfl).2 ⟨hb, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hcl, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hccl, fun h => by cases h⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hod⟩ (.cons ⟨⟨_, rfl⟩, hed⟩ (.cons ⟨⟨_, rfl⟩, hrd⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hcc', fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hcd', fun h => by cases h⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hzip⟩ (.cons ⟨⟨_, rfl⟩, hgrp⟩ (.cons ⟨⟨_, rfl⟩, haf⟩ .nil))))))))))))

theorem decode_acct {A : List FVal} (hA : AccountRecord.Valid A) :
    AccountRecord.decode (acctOf A).bytes = some A := by
  rw [acctOf_bytes hA]
  exact Schema.decode_encode (by decide) hA

theorem decode_tcat {c : List FVal} (hc : TranCatBalRecord.Valid c) :
    TranCatBalRecord.decode (tcatOf c).bytes = some c := by
  rw [tcatOf_bytes hc]
  exact Schema.decode_encode (by decide) hc

/-- The category balance record `2700-UPDATE-TCATBAL` creates. -/
theorem newCat_valid {acct : Int} {ty : List UInt8} {cd bal : Int} {fill : List UInt8}
    (ha : acct.natAbs < 100000000000) (ha0 : 0 ≤ acct) (hty : ty.length = 2)
    (hcd : cd.natAbs < 10000) (hcd0 : 0 ≤ cd) (hbal : bal.natAbs < 100000000000)
    (hfill : fill.length = 22) :
    TranCatBalRecord.Valid [.num acct, .str ty, .num cd, .num bal, .str fill] :=
  .cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨ha, fun _ => ha0⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hty⟩ (.cons ⟨_, rfl, by decide, by decide,
      (holds_display rfl).2 ⟨hcd, fun _ => hcd0⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hbal, fun h => by cases h⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hfill⟩ .nil))))

/-- The category balance record with a new balance (the REWRITE of `2700-UPDATE-TCATBAL`). -/
theorem tcatOf_setBal {c : List FVal} (hc : TranCatBalRecord.Valid c) (v : Int) :
    tcatOf (c.set 3 (.num v)) = { tcatOf c with bal := v } ∧
      (v.natAbs < 100000000000 → TranCatBalRecord.Valid (c.set 3 (.num v))) := by
  obtain ⟨acct, ty, cd, bal, fill, rfl, ha, ha0, hty, hcd, hcd0, -, hfill⟩ := tcat_shape hc
  exact ⟨rfl, fun hv => newCat_valid ha ha0 hty hcd hcd0 hv hfill⟩

theorem noCatMsg_text : CardDemo.Cbtrn02c.noCatMsg.map cp037Code =
    txt "TCATBAL record not found for key : " := by decide +kernel
theorem creatingMsg_text : CardDemo.Cbtrn02c.creatingMsg.map cp037Code = txt ".. Creating." := by
  decide +kernel

/-- The line `2700-UPDATE-TCATBAL` displays for a missing key. -/
theorem noCat_text (acct : Int) (ty : List UInt8) (cd : Int) :
    (CardDemo.Cbtrn02c.noCatMsg ++ catKeyB acct ty cd ++ CardDemo.Cbtrn02c.creatingMsg).map
      cp037Code = noCatLine acct ty cd := by
  simp only [catKeyB, List.map_append, noCatMsg_text, creatingMsg_text,
    text_unsigned (fmt := CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt) rfl rfl (by decide),
    text_unsigned (fmt := CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt) rfl rfl (by decide), noCatLine,
    List.append_assoc]

/-! ## Keyed lookups: coblean's and the translations' -/

@[simp] theorem tranOf_card (t : List FVal) : (tranOf t).card = tCard t := rfl
@[simp] theorem tranOf_ty (t : List FVal) : (tranOf t).ty = tType t := rfl
@[simp] theorem tranOf_cat (t : List FVal) : (tranOf t).cat = tCat t := rfl
@[simp] theorem tranOf_amt (t : List FVal) : (tranOf t).amt = tAmt t := rfl
@[simp] theorem tranOf_orig (t : List FVal) : (tranOf t).orig = tOrig t := rfl
@[simp] theorem xrefOf_acct (x : List FVal) : (xrefOf x).acct = xAcct x := rfl
@[simp] theorem acctOf_exp (a : List FVal) : (acctOf a).exp = aExp a := rfl
@[simp] theorem acctOf_limit (a : List FVal) : (acctOf a).limit = aLimit a := rfl
@[simp] theorem acctOf_cc (a : List FVal) : (acctOf a).cc = aCC a := rfl
@[simp] theorem acctOf_cd (a : List FVal) : (acctOf a).cd = aCD a := rfl
@[simp] theorem acctOf_bal (a : List FVal) : (acctOf a).bal = aBal a := rfl
@[simp] theorem tcatOf_key (c : List FVal) : (tcatOf c).key = catKeyB (cAcct c) (cType c) (cCd c) :=
  rfl
@[simp] theorem tcatOf_bal (c : List FVal) : (tcatOf c).bal = cBal c := rfl
@[simp] theorem tcatOf_fill (c : List FVal) : (tcatOf c).fill = cFill c := rfl

/-- A keyed lookup finds nothing when the translations' search finds nothing. -/
theorem findKey_none {α : Type} [Inhabited α] {k : KeyDecl} {v : List UInt8} {g : α → List UInt8}
    {p : α → Bool} {l : List α} (hp : ∀ x ∈ l, (Sem.keyOf k (g x) == v) = p x)
    (h : l.find? p = none) : Sem.findKey k v (l.map g) = none := by
  have := findKey_map k v g p l hp
  rw [h] at this
  cases hf : Sem.findKey k v (l.map g) with
  | none => rfl
  | some i => rw [hf] at this; cases this

/-- A keyed lookup finds the record the translations' search finds. -/
theorem findKey_some {α : Type} [Inhabited α] {k : KeyDecl} {v : List UInt8} {g : α → List UInt8}
    {p : α → Bool} {l : List α} (hp : ∀ x ∈ l, (Sem.keyOf k (g x) == v) = p x) {x : α}
    (h : l.find? p = some x) :
    ∃ i, Sem.findKey k v (l.map g) = some i ∧ i < l.length ∧ l.getD i default = x := by
  have := findKey_map k v g p l hp
  rw [h] at this
  cases hf : Sem.findKey k v (l.map g) with
  | none => rw [hf] at this; cases this
  | some i =>
    rw [hf] at this
    have hi : i < l.length := by simpa using findKey_lt' hf
    exact ⟨i, rfl, hi, Option.some.inj this⟩

/-- coblean's `List.set` at the index of a keyed lookup is the translations' `replaceFirst`. -/
theorem replaceFirst_eq_set {α : Type} {k : KeyDecl} {v : List UInt8} {g : α → List UInt8}
    {p : α → Bool} (y : α) : ∀ {l : List α} {j : Nat}, (∀ x ∈ l, (Sem.keyOf k (g x) == v) = p x) →
      Sem.findKey k v (l.map g) = some j → replaceFirst p y l = l.set j y
  | [], _, _, h => by simp [Sem.findKey] at h
  | x :: xs, j, hp, h => by
    simp only [List.map_cons, Sem.findKey] at h
    rw [hp x (List.mem_cons_self ..)] at h
    simp only [replaceFirst]
    cases hpx : p x
    · simp only [hpx, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [replaceFirst_eq_set y (fun z hz => hp z (List.mem_cons_of_mem _ hz)) hj']
      rfl
    · simp only [hpx, ↓reduceIte] at h ⊢
      cases h
      rfl

theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?_cons, h x (List.mem_cons_self ..),
      find?_congr (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem replaceFirst_congr {α : Type} {p q : α → Bool} (y : α) :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → replaceFirst p y l = replaceFirst q y l
  | [], _ => rfl
  | x :: xs, h => by
    simp only [replaceFirst, h x (List.mem_cons_self ..),
      replaceFirst_congr y (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem mem_replaceFirst {α : Type} {p : α → Bool} {y z : α} :
    ∀ {l : List α}, z ∈ replaceFirst p y l → z = y ∨ z ∈ l
  | [], h => by simp [replaceFirst] at h
  | x :: xs, h => by
    simp only [replaceFirst] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact .inr (by simp [h])
      · rcases mem_replaceFirst h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)

theorem find?_replaceFirst_same {α : Type} (p : α → Bool) (y : α) (hy : p y = true) :
    ∀ l : List α, (replaceFirst p y l).find? p = (l.find? p).map (fun _ => y)
  | [] => rfl
  | x :: xs => by
    simp only [replaceFirst]
    cases hx : p x
    · simp [hx, find?_replaceFirst_same p y hy xs]
    · simp [hy, hx]

theorem find?_replaceFirst_other {α : Type} {p q : α → Bool} (y : α) (hy : q y = false)
    (hpq : ∀ x, p x = true → q x = false) :
    ∀ l : List α, (replaceFirst p y l).find? q = l.find? q
  | [] => rfl
  | x :: xs => by
    simp only [replaceFirst]
    cases hx : p x
    · simp [List.find?_cons, find?_replaceFirst_other y hy hpq xs]
    · simp [hy, hpq x hx]

theorem find?_insertCat_other {q : TCat → Bool} {c : TCat} (hc : q c = false) :
    ∀ l : List TCat, (CardDemo.Cbtrn02c.insertCat c l).find? q = l.find? q
  | [] => by simp [CardDemo.Cbtrn02c.insertCat, hc]
  | x :: xs => by
    simp only [CardDemo.Cbtrn02c.insertCat]
    split
    · simp [List.find?_cons, hc]
    · simp [List.find?_cons, find?_insertCat_other hc xs]

theorem find?_insertCat_same {q : TCat → Bool} {c : TCat} (hc : q c = true) :
    ∀ l : List TCat, l.find? q = none → (CardDemo.Cbtrn02c.insertCat c l).find? q = some c
  | [], _ => by simp [CardDemo.Cbtrn02c.insertCat, hc]
  | x :: xs, h => by
    cases hx : q x
    · have h' : xs.find? q = none := by simpa [List.find?_cons, hx] using h
      simp only [CardDemo.Cbtrn02c.insertCat]
      split
      · simp [hc]
      · simp [hx, find?_insertCat_same hc xs h']
    · simp [hx] at h

theorem getD_map_lt {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {l : List α} {i : Nat}
    (h : i < l.length) : (l.map f).getD i default = f (l.getD i default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The key of a cross-reference record: its card number. -/
theorem xref_key {X : List FVal} (hX : CardXrefRecord.Valid X) :
    Sem.keyOf { off := 0, len := 16 } (xrefOf X).bytes = xCard X := by
  obtain ⟨card, cust, acct, fill, rfl, hcard, -⟩ := xref_shape hX
  simp only [Sem.keyOf, List.drop_zero, Xref.bytes, xrefOf, List.append_assoc]
  exact List.take_left' hcard

/-- The key of an account record: its id. -/
theorem acct_key (A : List FVal) :
    Sem.keyOf { off := 0, len := 11 } (acctOf A).bytes =
      encodeNum {} CardDemo.Cbtrn02c.FD_ACCT_ID.fmt (aId A) := by
  have hl : (encodeNum {} CardDemo.Cbtrn02c.ACCT_ID.fmt (aId A)).length = 11 :=
    (length_encodeNum {} CardDemo.Cbtrn02c.ACCT_ID.fmt _ (by decide)).trans rfl
  simp only [Sem.keyOf, List.drop_zero, Acct.bytes, acctOf, List.append_assoc]
  exact List.take_left' hl

theorem acct_holds {A : List FVal} (hA : AccountRecord.Valid A) :
    CardDemo.Cbtrn02c.FD_ACCT_ID.fmt.Holds {} (aId A) := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, hid, hid0, -⟩ := acct_shape hA
  exact (holds_display rfl).2 ⟨hid, fun _ => hid0⟩

theorem xref_holds {X : List FVal} (hX : CardXrefRecord.Valid X) :
    CardDemo.Cbtrn02c.FD_ACCT_ID.fmt.Holds {} (xAcct X) := by
  obtain ⟨card, cust, acct, fill, rfl, -, -, -, ha, ha0, -⟩ := xref_shape hX
  exact (holds_display rfl).2 ⟨ha, fun _ => ha0⟩

/-- coblean's key comparison for the account file is the translations' id comparison. -/
theorem acct_beq {A X : List FVal} (hA : AccountRecord.Valid A) (hX : CardXrefRecord.Valid X) :
    (Sem.keyOf { off := 0, len := 11 } (acctOf A).bytes ==
      encodeNum {} CardDemo.Cbtrn02c.FD_ACCT_ID.fmt (xAcct X)) = (aId A == xAcct X) := by
  rw [acct_key A]
  exact encodeNum_beq (by decide) (by decide) (acct_holds hA) (xref_holds hX)

/-- The category keys of valid field values are equal exactly when the fields are. -/
theorem catKeyB_inj {a1 a2 : Int} {t1 t2 : List UInt8} {c1 c2 : Int}
    (ha1 : CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt.Holds {} a1)
    (ha2 : CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt.Holds {} a2)
    (ht1 : t1.length = 2) (ht2 : t2.length = 2)
    (hc1 : CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt.Holds {} c1)
    (hc2 : CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt.Holds {} c2)
    (h : catKeyB a1 t1 c1 = catKeyB a2 t2 c2) : a1 = a2 ∧ t1 = t2 ∧ c1 = c2 := by
  have l1 : ∀ a, (encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt a).length = 11 :=
    fun a => (length_encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt a (by decide)).trans rfl
  unfold catKeyB at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [l1, ht1, ht2])
  obtain ⟨h3, h4⟩ := List.append_inj h1 (by simp [l1])
  refine ⟨?_, h4, ?_⟩
  · have := decodeNum_encodeNum {} _ a1 (by decide) (by decide) ha1
    rw [h3, decodeNum_encodeNum {} _ a2 (by decide) (by decide) ha2] at this
    exact (Option.some.inj this).symm
  · have := decodeNum_encodeNum {} _ c1 (by decide) (by decide) hc1
    rw [h2, decodeNum_encodeNum {} _ c2 (by decide) (by decide) hc2] at this
    exact (Option.some.inj this).symm

/-- The translations' key test is the comparison of coblean's keys. -/
theorem catKey_eq {c : List FVal} (hc : TranCatBalRecord.Valid c) {acct : Int} {ty : List UInt8}
    {cd : Int} (ha : CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt.Holds {} acct) (hty : ty.length = 2)
    (hcd : CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt.Holds {} cd) :
    catKey acct ty cd c = ((tcatOf c).key == catKeyB acct ty cd) := by
  obtain ⟨a1, t1, c1, b1, f1, rfl, h1, h1', ht1, hc1, hc1', -, -⟩ := tcat_shape hc
  have ha1 : CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt.Holds {} a1 :=
    (holds_display rfl).2 ⟨h1, fun _ => h1'⟩
  have hcc1 : CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt.Holds {} c1 :=
    (holds_display rfl).2 ⟨hc1, fun _ => hc1'⟩
  simp only [catKey, tcatOf_key, cAcct, cType, cCd, numOf, strOf, List.getD_cons_zero,
    List.getD_cons_succ]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  · intro he
    obtain ⟨e1, e2, e3⟩ := catKeyB_inj ha1 ha ht1 hty hcc1 hcd he
    exact ⟨⟨e1, e2⟩, e3⟩

/-! ## The simulation -/

/-- The lines displayed by the events `l` (oldest first). -/
def dispL (l : List Event) : List (List UInt8) :=
  l.filterMap fun | .display bs => some bs | _ => none

/-- The records written to file `f` by the events `l`. -/
def wrL (f : Nat) (l : List Event) : List (List UInt8) :=
  l.filterMap fun | .write g bs => if g = f then some bs else none | _ => none

/-- The records rewritten in file `f` by the events `l`. -/
def rwL (f : Nat) (l : List Event) : List (List UInt8) :=
  l.filterMap fun | .rewrite g bs => if g = f then some bs else none | _ => none

theorem dispL_append (l l' : List Event) : dispL (l ++ l') = dispL l ++ dispL l' := by
  simp [dispL, List.filterMap_append]
theorem wrL_append (f : Nat) (l l' : List Event) : wrL f (l ++ l') = wrL f l ++ wrL f l' := by
  simp [wrL, List.filterMap_append]
theorem rwL_append (f : Nat) (l l' : List Event) : rwL f (l ++ l') = rwL f l ++ rwL f l' := by
  simp [rwL, List.filterMap_append]
theorem dispL_nil : dispL [] = [] := rfl
theorem wrL_nil (f : Nat) : wrL f [] = [] := rfl
theorem rwL_nil (f : Nat) : rwL f [] = [] := rfl
theorem dispL_display (bs : List UInt8) (l : List Event) :
    dispL (.display bs :: l) = bs :: dispL l := rfl
theorem dispL_write (g : Nat) (bs : List UInt8) (l : List Event) :
    dispL (.write g bs :: l) = dispL l := rfl
theorem dispL_rewrite (g : Nat) (bs : List UInt8) (l : List Event) :
    dispL (.rewrite g bs :: l) = dispL l := rfl
theorem wrL_display (f : Nat) (bs : List UInt8) (l : List Event) :
    wrL f (.display bs :: l) = wrL f l := rfl
theorem wrL_rewrite (f g : Nat) (bs : List UInt8) (l : List Event) :
    wrL f (.rewrite g bs :: l) = wrL f l := rfl
theorem wrL_write (f g : Nat) (bs : List UInt8) (l : List Event) :
    wrL f (.write g bs :: l) = if g = f then bs :: wrL f l else wrL f l := by
  by_cases h : g = f <;> simp [wrL, h]
theorem rwL_display (f : Nat) (bs : List UInt8) (l : List Event) :
    rwL f (.display bs :: l) = rwL f l := rfl
theorem rwL_write (f g : Nat) (bs : List UInt8) (l : List Event) :
    rwL f (.write g bs :: l) = rwL f l := rfl
theorem rwL_rewrite (f g : Nat) (bs : List UInt8) (l : List Event) :
    rwL f (.rewrite g bs :: l) = if g = f then bs :: rwL f l else rwL f l := by
  by_cases h : g = f <;> simp [rwL, h]

/-- The translations' state `S` after the same daily transactions as coblean's model state `M`:
the same accounts (in the same order), the same category balance records for every key (the
first record with the key: the translations append a new record, coblean inserts it in key
order), the same `FILLER`, the same rejects, and the outputs of `M`'s events. -/
structure Corr (S : St) (M : CardDemo.Cbtrn02c.Model) : Prop where
  accts : M.accts = S.accts.map acctOf
  aval : ∀ a ∈ S.accts, AccountRecord.Valid a
  cval : ∀ c ∈ S.cats, TranCatBalRecord.Valid c
  klen : ∀ c ∈ M.cats, c.key.length = 17
  cats : ∀ v, M.cats.find? (fun c => c.key == v) =
    (S.cats.find? (fun c => (tcatOf c).key == v)).map tcatOf
  fill : M.catFill = S.catFill
  flen : S.catFill.length = 22
  rejects : M.rejects = S.rejects
  disp : S.disp = txt "START OF EXECUTION OF PROGRAM CBTRN02C" ::
    (dispL M.out.reverse).map (·.map cp037Code)
  tranW : (wrL 2 M.out.reverse).map TranRecord.decode = S.tranW.map some
  rejW : (wrL 4 M.out.reverse).map RejectRecord.decode = S.rejW.map some
  catW : (wrL 6 M.out.reverse).map TranCatBalRecord.decode = S.catW.map some
  acctRW : (rwL 5 M.out.reverse).map AccountRecord.decode = S.acctRW.map some
  catRW : (rwL 6 M.out.reverse).map TranCatBalRecord.decode = S.catRW.map some

theorem key_eq (a : Int) (ty : List UInt8) (c : Int) :
    encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt a ++ ty ++
      encodeNum {} CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt c = catKeyB a ty c := rfl

theorem post_corr {S : St} {M : CardDemo.Cbtrn02c.Model} {T X A : List FVal} {j : Nat}
    {clk : List UInt8} (hC : Corr S M) (hT : DalytranRecord.Valid T) (hX : CardXrefRecord.Valid X)
    (hA : AccountRecord.Valid A) (hAX : aId A = xAcct X)
    (hj : Sem.findKey { off := 0, len := 11 } (encodeNum {} CardDemo.Cbtrn02c.FD_ACCT_ID.fmt (xAcct X))
      (S.accts.map (fun a => (acctOf a).bytes)) = some j)
    (hclk : 16 ≤ clk.length) :
    Corr (St.post clk S T X A)
      (CardDemo.Cbtrn02c.Model.post (fun _ => clk) (sp 20) M (tranOf T) (xrefOf X) j (acctOf A)) := by
  obtain ⟨hacc, haval, hcval, hklen, hcats, hfill, hflen, hrej, hdisp, htr, hrj, hcw, harw, hcrw⟩ := hC
  obtain ⟨-, htyl, hcatb, hcat0, -, -, hamtb, -⟩ := tranOf_valid hT
  obtain ⟨-, -, hxab, hxa0, -⟩ := xrefOf_valid hX
  have hKa : CardDemo.Cbtrn02c.FD_TRANCAT_ACCT_ID.fmt.Holds {} (xAcct X) :=
    (holds_display rfl).2 ⟨hxab, fun _ => hxa0⟩
  have hKc : CardDemo.Cbtrn02c.FD_TRANCAT_CD.fmt.Holds {} (tCat T) :=
    (holds_display rfl).2 ⟨hcatb, fun _ => hcat0⟩
  have hfcK : findCat S.cats (xAcct X) (tType T) (tCat T) =
      S.cats.find? (fun c => (tcatOf c).key == catKeyB (xAcct X) (tType T) (tCat T)) :=
    find?_congr (fun c hc => catKey_eq (hcval c hc) hKa htyl hKc)
  have hpk : ∀ c ∈ M.cats, (Sem.keyOf { off := 0, len := 17 } c.bytes ==
      catKeyB (xAcct X) (tType T) (tCat T)) = (c.key == catKeyB (xAcct X) (tType T) (tCat T)) :=
    fun c hc => by rw [CardDemo.Cbtrn02c.keyOf_cat c (hklen c hc)]
  have hMK := hcats (catKeyB (xAcct X) (tType T) (tCat T))
  have hset : replaceFirst (fun b => aId b == aId A) (postAcct A (tAmt T)) S.accts =
      S.accts.set j (postAcct A (tAmt T)) :=
    replaceFirst_eq_set (k := { off := 0, len := 11 })
      (v := encodeNum {} CardDemo.Cbtrn02c.FD_ACCT_ID.fmt (xAcct X)) (g := fun a => (acctOf a).bytes)
      (p := fun b => aId b == aId A) _ (fun b hb => by rw [acct_beq (haval b hb) hX, hAX]) hj
  unfold St.post CardDemo.Cbtrn02c.Model.post
  rw [← acctOf_post hA (tranOf T).amt]
  simp only [tranOf_ty, tranOf_cat, tranOf_amt, xrefOf_acct, key_eq]
  cases hS : S.cats.find? (fun c => (tcatOf c).key == catKeyB (xAcct X) (tType T) (tCat T)) with
  | none =>
    have hMK' : M.cats.find? (fun c => c.key == catKeyB (xAcct X) (tType T) (tCat T)) = none := by
      rw [hMK, hS]; rfl
    simp only [hfcK, hS, findKey_none hpk hMK']
    rw [hset, hfill]
    have hnew : ({ key := catKeyB (xAcct X) (tType T) (tCat T), bal := tAmt T, fill := S.catFill } :
        TCat) = tcatOf [.num (xAcct X), .str (tType T), .num (tCat T), .num (tAmt T), .str S.catFill] :=
      rfl
    have hnv : TranCatBalRecord.Valid
        [.num (xAcct X), .str (tType T), .num (tCat T), .num (tAmt T), .str S.catFill] :=
      newCat_valid hxab hxa0 htyl hcatb hcat0 hamtb hflen
    rw [hnew]
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, hflen, hrej, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · rw [hacc, List.map_set]
    · intro a ha
      rcases List.mem_or_eq_of_mem_set ha with ha | rfl
      · exact haval a ha
      · exact postAcct_valid hA _
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hcval c hc
      · rw [List.mem_singleton] at hc; subst hc; exact hnv
    · intro c hc
      rcases CardDemo.Cbtrn02c.mem_insertCat hc with rfl | hc
      · exact catKeyB_length _ _ _ htyl
      · exact hklen c hc
    · intro v
      by_cases hv : catKeyB (xAcct X) (tType T) (tCat T) = v
      · subst hv
        rw [find?_insertCat_same (q := fun c => c.key == catKeyB (xAcct X) (tType T) (tCat T))
          (beq_iff_eq.2 rfl) _ hMK', List.find?_append, hS]
        simp [tcatOf, cAcct, cType, cCd, numOf, strOf]
      · have hq : ((tcatOf [.num (xAcct X), .str (tType T), .num (tCat T), .num (tAmt T),
            .str S.catFill]).key == v) = false := beq_eq_false_iff_ne.2 hv
        rw [find?_insertCat_other hq, hcats v, List.find?_append]
        simp only [List.find?_cons, hq, List.find?_nil]
        cases S.cats.find? (fun c => (tcatOf c).key == v) <;> rfl
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        dispL_append, dispL_display, dispL_write, dispL_rewrite, dispL_nil]
      rw [hdisp, List.map_append, List.map_singleton, ← List.append_assoc, noCat_text]
      rfl
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        wrL_append, wrL_display, wrL_write, wrL_rewrite, wrL_nil]
      simp [htr, decode_tranRec hT hclk]
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        wrL_append, wrL_display, wrL_write, wrL_rewrite, wrL_nil]
      simp [hrj]
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        wrL_append, wrL_display, wrL_write, wrL_rewrite, wrL_nil]
      simp [hcw, decode_tcat hnv]
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        rwL_append, rwL_display, rwL_write, rwL_rewrite, rwL_nil]
      simp [harw, decode_acct (postAcct_valid hA _)]
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        rwL_append, rwL_display, rwL_write, rwL_rewrite, rwL_nil]
      simp [hcrw]
  | some cv =>
    have hMK' : M.cats.find? (fun c => c.key == catKeyB (xAcct X) (tType T) (tCat T)) =
        some (tcatOf cv) := by
      rw [hMK, hS]; rfl
    obtain ⟨k, hk, hkl, hkc⟩ := findKey_some hpk hMK'
    have hcvm : cv ∈ S.cats := List.mem_of_find?_eq_some hS
    have hcv := hcval cv hcvm
    simp only [hfcK, hS, hk, hkc]
    rw [hset]
    have hcK : (tcatOf cv).key = catKeyB (xAcct X) (tType T) (tCat T) := by
      have := List.find?_some hS
      exact beq_iff_eq.1 this
    have hcv' := tcatOf_setBal hcv (Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt (cBal cv + tAmt T)).2
    have hc' : (⟨(tcatOf cv).key,
        (Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt ((tcatOf cv).bal + tAmt T)).2,
        (tcatOf cv).fill⟩ : TCat) =
        tcatOf (cv.set 3 (.num (Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt (cBal cv + tAmt T)).2)) :=
      hcv'.1.symm
    have hv' := hcv'.2 (CardDemo.Cbtrn02c.fitNum_catBal _)
    have hkey' := congrArg TCat.key hcv'.1
    rw [hc']
    generalize cv.set 3 (.num (Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt (cBal cv + tAmt T)).2) = cv'
      at hv' hkey' ⊢
    simp only [hcK] at hkey'
    have hSset : replaceFirst (catKey (xAcct X) (tType T) (tCat T)) cv' S.cats =
        replaceFirst (fun c => (tcatOf c).key == catKeyB (xAcct X) (tType T) (tCat T)) cv' S.cats :=
      replaceFirst_congr cv' (fun c hc => catKey_eq (hcval c hc) hKa htyl hKc)
    have hMset : M.cats.set k (tcatOf cv') =
        replaceFirst (fun c => c.key == catKeyB (xAcct X) (tType T) (tCat T)) (tcatOf cv') M.cats :=
      (replaceFirst_eq_set (tcatOf cv') hpk hk).symm
    rw [hSset, hMset]
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, (tcatOf_valid hcv).2.2, hrej, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only
    · rw [hacc, List.map_set]
    · intro a ha
      rcases List.mem_or_eq_of_mem_set ha with ha | rfl
      · exact haval a ha
      · exact postAcct_valid hA _
    · intro c hc
      rcases mem_replaceFirst hc with rfl | hc
      · exact hv'
      · exact hcval c hc
    · intro c hc
      rcases mem_replaceFirst hc with rfl | hc
      · exact (tcatOf_valid hv').1
      · exact hklen c hc
    · intro v
      by_cases hv : catKeyB (xAcct X) (tType T) (tCat T) = v
      · subst hv
        rw [find?_replaceFirst_same (fun c : TCat => c.key == catKeyB (xAcct X) (tType T) (tCat T))
            _ (beq_iff_eq.2 hkey'), hMK',
          find?_replaceFirst_same
            (fun c : List FVal => (tcatOf c).key == catKeyB (xAcct X) (tType T) (tCat T))
            _ (beq_iff_eq.2 hkey'), hS]
        rfl
      · have hq : ((tcatOf cv').key == v) = false := by rw [hkey']; exact beq_eq_false_iff_ne.2 hv
        have hpq : ∀ c : TCat, (c.key == catKeyB (xAcct X) (tType T) (tCat T)) = true →
            (c.key == v) = false := by
          intro c hc; rw [beq_iff_eq.1 hc]; exact beq_eq_false_iff_ne.2 hv
        rw [find?_replaceFirst_other (p := fun c : TCat => c.key == catKeyB (xAcct X) (tType T) (tCat T))
            (q := fun c : TCat => c.key == v) _ hq hpq, hcats v,
          find?_replaceFirst_other
            (p := fun c : List FVal => (tcatOf c).key == catKeyB (xAcct X) (tType T) (tCat T))
            (q := fun c : List FVal => (tcatOf c).key == v) _ hq (fun c hc => hpq (tcatOf c) hc)]
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        dispL_append, dispL_write, dispL_rewrite, dispL_nil, List.append_nil]
      exact hdisp
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        wrL_append, wrL_write, wrL_rewrite, wrL_nil]
      simp [htr, decode_tranRec hT hclk]
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        wrL_append, wrL_write, wrL_rewrite, wrL_nil]
      simp [hrj]
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        wrL_append, wrL_write, wrL_rewrite, wrL_nil]
      simp [hcw]
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        rwL_append, rwL_write, rwL_rewrite, rwL_nil]
      simp [harw, decode_acct (postAcct_valid hA _)]
    · simp only [List.reverse_cons, List.nil_append, List.append_assoc, List.cons_append,
        rwL_append, rwL_write, rwL_rewrite, rwL_nil]
      simp [hcrw, decode_tcat hv']

theorem reject_corr {S : St} {M : CardDemo.Cbtrn02c.Model} {T : List FVal} (hC : Corr S M)
    (hT : DalytranRecord.Valid T) (code : Int) {desc : List UInt8} (hd : desc.length ≤ 76) :
    Corr (S.reject T code desc) (M.reject (tranOf T) code desc) := by
  obtain ⟨hacc, haval, hcval, hklen, hcats, hfill, hflen, hrej, hdisp, htr, hrj, hcw, harw, hcrw⟩ := hC
  refine ⟨hacc, haval, hcval, hklen, hcats, hfill, hflen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [St.reject, CardDemo.Cbtrn02c.Model.reject, List.reverse_cons, dispL_append,
      wrL_append, rwL_append, dispL_write, dispL_nil, wrL_write, wrL_nil, rwL_write, rwL_nil,
      List.append_nil]
  · rw [hrej]
  · exact hdisp
  · simpa using htr
  · simp [hrj, decode_reject hT code hd]
  · simpa using hcw
  · exact harw
  · exact hcrw

/-- **One daily transaction**: the translations' step and coblean's `step` keep `Corr`. -/
theorem step_corr {xrefs : List (List FVal)} {clk : List UInt8} {S : St}
    {M : CardDemo.Cbtrn02c.Model} {T : List FVal} (hC : Corr S M) (hT : DalytranRecord.Valid T)
    (hX : ∀ x ∈ xrefs, CardXrefRecord.Valid x) (hclk : 16 ≤ clk.length) :
    Corr (Model.step xrefs clk S T)
      (CardDemo.Cbtrn02c.step (xrefs.map xrefOf) (fun _ => clk) (sp 20) M (tranOf T)) := by
  have hpx : ∀ x ∈ xrefs.map xrefOf, (Sem.keyOf { off := 0, len := 16 } x.bytes == tCard T) =
      (x.card == tCard T) := by
    intro x hx
    obtain ⟨X, hXm, rfl⟩ := List.mem_map.1 hx
    rw [xref_key (hX X hXm)]
    rfl
  have hfx : (xrefs.map xrefOf).find? (fun x => x.card == tCard T) =
      (findXref xrefs (tCard T)).map xrefOf := by
    rw [List.find?_map]; rfl
  unfold Model.step CardDemo.Cbtrn02c.step
  simp only [tranOf_card]
  cases hf : findXref xrefs (tCard T) with
  | none =>
    rw [hf] at hfx
    simp only [findKey_none hpx hfx]
    exact reject_corr hC hT 100 (by decide)
  | some X =>
    rw [hf] at hfx
    obtain ⟨i, hi, -, hiX⟩ := findKey_some hpx hfx
    have hXv : CardXrefRecord.Valid X := hX X (List.mem_of_find?_eq_some hf)
    simp only [hi, hiX, xrefOf_acct]
    have hpa : ∀ a ∈ S.accts, (Sem.keyOf { off := 0, len := 11 } ((fun a => (acctOf a).bytes) a) ==
        encodeNum {} CardDemo.Cbtrn02c.FD_ACCT_ID.fmt (xAcct X)) = (fun a => aId a == xAcct X) a :=
      fun a ha => acct_beq (hC.aval a ha) hXv
    have hmap : M.accts.map Acct.bytes = S.accts.map (fun a => (acctOf a).bytes) := by
      rw [hC.accts, List.map_map]; rfl
    rw [hmap]
    cases ha : findAcct S.accts (xAcct X) with
    | none =>
      simp only [findKey_none hpa ha]
      exact reject_corr hC hT 101 (by decide)
    | some A =>
      obtain ⟨j, hj, hjl, hjA⟩ := findKey_some hpa ha
      have hAm : A ∈ S.accts := List.mem_of_find?_eq_some ha
      have hAv := hC.aval A hAm
      have hAX : aId A = xAcct X := by
        have := List.find?_some ha
        exact beq_iff_eq.1 this
      have hMa : M.accts.getD j default = acctOf A := by
        rw [hC.accts, getD_map_lt acctOf hjl, hjA]
      simp only [hj, hMa, acctOf_exp, tranOf_orig, acctOf_limit, acctOf_cc, acctOf_cd, tranOf_amt]
      by_cases h103 : Sem.cmpBytes (aExp A) ((tOrig T).take 10) = .lt
      · simp only [h103, ↓reduceIte]
        exact reject_corr hC hT 103 (by decide)
      · simp only [h103, ↓reduceIte]
        by_cases h102 : aLimit A <
            (Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt (aCC A - aCD A + tAmt T)).2
        · simp only [h102, ↓reduceIte]
          exact reject_corr hC hT 102 (by decide)
        · simp only [h102, ↓reduceIte]
          exact post_corr hC hT hXv hAv hAX hj hclk

/-- The daily transactions `ts`, from corresponding states. -/
theorem fold_corr {xrefs : List (List FVal)} {clk : List UInt8}
    (hX : ∀ x ∈ xrefs, CardXrefRecord.Valid x) (hclk : 16 ≤ clk.length) :
    ∀ (ts : List (List FVal)) (S : St) (M : CardDemo.Cbtrn02c.Model), Corr S M →
      (∀ t ∈ ts, DalytranRecord.Valid t) →
      Corr (ts.foldl (Model.step xrefs clk) S)
        (ts.foldl (fun m t => CardDemo.Cbtrn02c.step (xrefs.map xrefOf) (fun _ => clk) (sp 20) m
          (tranOf t)) M)
  | [], _, _, hC, _ => hC
  | t :: ts, _, _, hC, ht =>
    fold_corr hX hclk ts _ _ (step_corr hC (ht t (by simp)) hX hclk)
      (fun t' h' => ht t' (by simp [h']))

/-! ## The COBOL run -/

cobol_mem_hex initMem from "init_mem.hex"

set_option maxRecDepth 10000 in
theorem initMem_size : initMem.size = 3252 := by rfl

/-- The harness storage holds spaces in the `FILLER`s of WORKING-STORAGE's `TRAN-RECORD` and
`TRAN-CAT-BAL-RECORD`. -/
theorem initMem_tfill : initMem.read 2212 20 = sp 20 := by decide +kernel
theorem initMem_catFill : initMem.read 2618 22 = sp 22 := by decide +kernel

theorem startMsg_text : CardDemo.Cbtrn02c.startMsg.map cp037Code =
    txt "START OF EXECUTION OF PROGRAM CBTRN02C" := by decide +kernel
theorem endMsg_text : CardDemo.Cbtrn02c.endMsg.map cp037Code =
    txt "END OF EXECUTION OF PROGRAM CBTRN02C" := by decide +kernel
theorem procMsg_text :
    CardDemo.Cbtrn02c.procMsg.map cp037Code = txt "TRANSACTIONS PROCESSED :" := by decide +kernel
theorem rejMsg_text :
    CardDemo.Cbtrn02c.rejMsg.map cp037Code = txt "TRANSACTIONS REJECTED  :" := by decide +kernel

/-- The texts of the counts (`PIC 9(09)`). -/
theorem trCount_text (k : Nat) :
    (encodeNum {} CardDemo.Cbtrn02c.WS_TRANSACTION_COUNT.fmt (k : Int)).map cp037Code = zpad 9 k :=
  text_unsigned rfl rfl (by decide) _
theorem rjCount_text (k : Nat) :
    (encodeNum {} CardDemo.Cbtrn02c.WS_REJECT_COUNT.fmt (k : Int)).map cp037Code = zpad 9 k :=
  text_unsigned rfl rfl (by decide) _

/-- The state before the first transaction. -/
theorem init_corr {accts cats : List (List FVal)} (hv3 : ∀ v ∈ accts, AccountRecord.Valid v)
    (hv4 : ∀ v ∈ cats, TranCatBalRecord.Valid v) :
    Corr (init accts cats) ⟨accts.map acctOf, cats.map tcatOf, sp 22, 0, 0, []⟩ := by
  refine ⟨rfl, hv3, hv4, ?_, ?_, rfl, by simp [init, sp], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
    exact (tcatOf_valid (hv4 c0 hc0)).1
  · intro v
    rw [List.find?_map]
    rfl

/-- coblean's theorem `cbtrn02c_posts`, for the inputs as coblean's structures. -/
theorem cobol_run (vals1 vals2 vals3 vals4 : List (List FVal)) (clk : List UInt8)
    (hv1 : ∀ v ∈ vals1, DalytranRecord.Valid v) (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, AccountRecord.Valid v) (hv4 : ∀ v ∈ vals4, TranCatBalRecord.Valid v)
    (hc : CurrentDate clk) (hids : (vals1.map tId).Nodup) (hlen : vals1.length < 1000000000)
    (n : Nat) (hn : vals1.length < n) :
    let r := CardDemo.Cbtrn02c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbtrn02c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (3, vals2.map CardXrefRecord.encode), (5, vals3.map AccountRecord.encode),
        (6, vals4.map TranCatBalRecord.encode)])
    let M := vals1.foldl (fun m t => CardDemo.Cbtrn02c.step (vals2.map xrefOf) (fun _ => clk) (sp 20) m
      (tranOf t)) ⟨vals3.map acctOf, vals4.map tcatOf, sp 22, 0, 0, []⟩
    r.1 = .stop .goback ∧
      r.2.out = [.display CardDemo.Cbtrn02c.endMsg,
        .display (CardDemo.Cbtrn02c.rejMsg ++ encodeNum {} CardDemo.Cbtrn02c.WS_REJECT_COUNT.fmt M.rejects),
        .display (CardDemo.Cbtrn02c.procMsg ++
          encodeNum {} CardDemo.Cbtrn02c.WS_TRANSACTION_COUNT.fmt vals1.length)] ++ M.out ++
        [.display CardDemo.Cbtrn02c.startMsg] ∧
      r.2.mem.read 3250 2 =
        encodeNum {} CardDemo.Cbtrn02c.RETURN_CODE.fmt (if 0 < M.rejects then 4 else 0) := by
  have hf1 : vals1.map DalytranRecord.encode = (vals1.map tranOf).map Tran.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun t ht => (tranOf_bytes (hv1 t ht)).symm)
  have hf2 : vals2.map CardXrefRecord.encode = (vals2.map xrefOf).map Xref.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun x hx => (xrefOf_bytes (hv2 x hx)).symm)
  have hf3 : vals3.map AccountRecord.encode = (vals3.map acctOf).map Acct.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun a ha => (acctOf_bytes (hv3 a ha)).symm)
  have hf4 : vals4.map TranCatBalRecord.encode = (vals4.map tcatOf).map TCat.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun c hc => (tcatOf_bytes (hv4 c hc)).symm)
  have hpost := CardDemo.Cbtrn02c.cbtrn02c_posts initMem initMem_size (fun _ => clk)
    (fun _ => EquivLean.Modernize.Cbact04c.Glue.clock_ok hc) (vals1.map tranOf)
    (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht; exact tranOf_valid (hv1 t0 ht0))
    (by rw [List.map_map]; exact hids) (by rw [List.length_map]; exact hlen)
    (vals2.map xrefOf)
    (by intro x hx; obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx; exact xrefOf_valid (hv2 x0 hx0))
    (vals3.map acctOf)
    (by intro a ha; obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha; exact acctOf_valid (hv3 a0 ha0))
    (vals4.map tcatOf)
    (by intro c hc; obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc; exact tcatOf_valid (hv4 c0 hc0))
    n (by rw [List.length_map]; exact hn)
  simp only [initMem_tfill, initMem_catFill, ← hf1, ← hf2, ← hf3, ← hf4, CardDemo.Cbtrn02c.model,
    List.foldl_map, List.length_map] at hpost
  exact hpost

/-- **CBTRN02C's COBOL run outputs what `Model.run` says**, for valid field values with distinct
transaction ids, fewer than 10^9 transactions, and a `CURRENT-DATE` clock reading. -/
theorem cobol_outputs_core (vals1 vals2 vals3 vals4 : List (List FVal)) (clk : List UInt8)
    (hv1 : ∀ v ∈ vals1, DalytranRecord.Valid v) (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, AccountRecord.Valid v) (hv4 : ∀ v ∈ vals4, TranCatBalRecord.Valid v)
    (hc : CurrentDate clk) (hids : (vals1.map tId).Nodup) (hlen : vals1.length < 1000000000)
    (n : Nat) (hn : vals1.length < n) :
    let r := CardDemo.Cbtrn02c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbtrn02c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (3, vals2.map CardXrefRecord.encode), (5, vals3.map AccountRecord.encode),
        (6, vals4.map TranCatBalRecord.encode)])
    let o := Model.run vals1 vals2 vals3 vals4 clk
    r.1 = .stop .goback ∧ (displays r.2).map (·.map cp037Code) = o.disp ∧
      (writes 2 r.2).map TranRecord.decode = o.tranW.map some ∧
      (writes 4 r.2).map RejectRecord.decode = o.rejW.map some ∧
      (writes 6 r.2).map TranCatBalRecord.decode = o.catW.map some ∧
      (rewrites 5 r.2).map AccountRecord.decode = o.acctRW.map some ∧
      (rewrites 6 r.2).map TranCatBalRecord.decode = o.catRW.map some ∧
      itemValue CardDemo.Cbtrn02c.RETURN_CODE CardDemo.Cbtrn02c.RETURN_CODE.fmt r.2 = o.rc := by
  dsimp only
  obtain ⟨hstop, hout, hrc⟩ := cobol_run vals1 vals2 vals3 vals4 clk hv1 hv2 hv3 hv4 hc hids hlen n hn
  have hC := fold_corr hv2 (by rw [hc.1]; decide) vals1 _ _ (init_corr hv3 hv4) hv1
  generalize vals1.foldl (fun m t => CardDemo.Cbtrn02c.step (vals2.map xrefOf) (fun _ => clk) (sp 20) m
    (tranOf t)) ⟨vals3.map acctOf, vals4.map tcatOf, sp 22, 0, 0, []⟩ = M at hC hout hrc
  simp only [Model.run]
  generalize vals1.foldl (Model.step vals2 clk) (init vals3 vals4) = S at hC
  refine ⟨hstop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (dispL _).map _ = _
    rw [hout, hC.disp, hC.rejects]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc, dispL_append, dispL_display, dispL_nil, List.map_append,
      List.map_cons, List.map_nil, startMsg_text, endMsg_text, procMsg_text, rejMsg_text,
      trCount_text]
  · show (wrL 2 _).map _ = _
    rw [hout]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc, wrL_append, wrL_display, wrL_nil, List.append_nil]
    exact hC.tranW
  · show (wrL 4 _).map _ = _
    rw [hout]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc, wrL_append, wrL_display, wrL_nil, List.append_nil]
    exact hC.rejW
  · show (wrL 6 _).map _ = _
    rw [hout]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc, wrL_append, wrL_display, wrL_nil, List.append_nil]
    exact hC.catW
  · show (rwL 5 _).map _ = _
    rw [hout]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc, rwL_append, rwL_display, rwL_nil, List.append_nil]
    exact hC.acctRW
  · show (rwL 6 _).map _ = _
    rw [hout]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc, rwL_append, rwL_display, rwL_nil, List.append_nil]
    exact hC.catRW
  · show (decodeNum {} CardDemo.Cbtrn02c.RETURN_CODE.fmt (Cobol.Mem.read _ 3250 2)).getD 0 = _
    rw [hrc, hC.rejects, decodeNum_encodeNum {} _ _ (by decide) (by decide) (by split <;> decide)]
    rfl

/-- **CBTRN02C's COBOL run outputs what `Model.run` says**, for every input of the statements'
domain: valid field values, a `CURRENT-DATE` clock reading, distinct transaction ids and fewer
than 10^9 transactions (`Domain`).  The run ends with GOBACK; its displays (code points), the
records it writes to TRANSACT, DALYREJS and TCATBAL and rewrites in ACCOUNT and TCATBAL (decoded),
and RETURN-CODE are `Model.run`'s. -/
theorem cobol_outputs (vals1 vals2 vals3 vals4 : List (List FVal)) (clk : List UInt8)
    (hv1 : ∀ v ∈ vals1, DalytranRecord.Valid v) (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, AccountRecord.Valid v) (hv4 : ∀ v ∈ vals4, TranCatBalRecord.Valid v)
    (hc : CurrentDate clk) (hD : Domain vals1 vals2 vals3 vals4) (n : Nat) (hn : vals1.length < n) :
    let r := CardDemo.Cbtrn02c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbtrn02c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (3, vals2.map CardXrefRecord.encode), (5, vals3.map AccountRecord.encode),
        (6, vals4.map TranCatBalRecord.encode)])
    let o := Model.run vals1 vals2 vals3 vals4 clk
    r.1 = .stop .goback ∧ (displays r.2).map (·.map cp037Code) = o.disp ∧
      (writes 2 r.2).map TranRecord.decode = o.tranW.map some ∧
      (writes 4 r.2).map RejectRecord.decode = o.rejW.map some ∧
      (writes 6 r.2).map TranCatBalRecord.decode = o.catW.map some ∧
      (rewrites 5 r.2).map AccountRecord.decode = o.acctRW.map some ∧
      (rewrites 6 r.2).map TranCatBalRecord.decode = o.catRW.map some ∧
      itemValue CardDemo.Cbtrn02c.RETURN_CODE CardDemo.Cbtrn02c.RETURN_CODE.fmt r.2 = o.rc :=
  cobol_outputs_core vals1 vals2 vals3 vals4 clk hv1 hv2 hv3 hv4 hc hD.1 hD.2 n hn

end EquivLean.Modernize.Cbtrn02c.Glue
