import EquivLean.Modernize.Cbstm03a.Domain
import EquivLean.Modernize.GlueKit
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Sorted
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Abend

/-!
# CBSTM03A: record-encoding bridge for `Glue.lean`

Connects the field-value schemas (`TrnxRecord`, `CardXrefRecord`, `CustomerRecord`, `AccountRecord`
from `cbstm03ab.ir.json`) to the byte-level projections and validity predicates used by
`Cobol.StmCore` (`stm_run_sorted`, `stm_run`, `stm_run_abort_cust`, `stm_run_abort_acct`):

* `trnx_fields`: length = 350, `tCard` (bytes `0..16`), `tId` (bytes `16..32`), `tDesc` (bytes `48..148`),
  `decodeNum` of `TRNX-AMT` (bytes `148..159`), `tAmt` = field 5, and `AmtOk (TrnxRecord.encode r)`.
* `xref_fields`: length = 50, `xCard` (bytes `0..16`), `decodeNum` of `XREF-CUST-ID` (`16..25`) and
  `XREF-ACCT-ID` (`25..36`), `xCid` = field 1, `xAid` = field 2, and `0 ≤ xCid`, `0 ≤ xAid`.
* `cust_fields`: length = 500, key `take 9 = digitChars 9 cid.natAbs`, name/address fields (`fld`),
  `decodeNum` of `CUST-FICO-CREDIT-SCORE` (`329..332`), and `cFico` = field 17.
* `acct_fields`: length = 300, key `take 11 = digitChars 11 aid.natAbs`, `decodeNum` of `ACCT-ID`
  (`0..11`) and `ACCT-CURR-BAL` (`12..24`), `aAid` = field 0, and `aBal` = field 2.
* `cust_key_beq` / `acct_key_beq` and `xok_of_find`: when `x` is a valid `CardXrefRecord` and
  `custs.find?` and `accts.find?` both find matching valid customer and account records `c` and `a`,
  `XOk` holds on `CardXrefRecord.encode x`, `custOf` = `CustomerRecord.encode c`, and
  `acctOf` = `AccountRecord.encode a`.
-/

open Cobol EquivLean.Cobol.Rec EquivLean.Modernize.GlueKit Cobol.StmCore

namespace EquivLean.Modernize.Cbstm03a.StmBridge

theorem getD_mem_of_lt {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-! ## Helper lemmas on `Schema.bytes_encode_getD` -/

theorem field_str_bytes {s : Schema} (hc : s.Contig) {vals : List FVal} (hv : s.Valid vals)
    (i o l : Nat) (hi : i < s.fields.length)
    (hkind : ∃ j, (s.fields.getD i default).desc.kind = .alnum j)
    (hroff : (s.fields.getD i default).roff = o)
    (hlen : (s.fields.getD i default).desc.len = l) :
    ((s.encode vals).drop o).take l = strOf (vals.getD i default) ∧
      (strOf (vals.getD i default)).length = l := by
  have hb := Schema.bytes_encode_getD hc hv i hi
  have hvi := Forall2.getD hv i hi
  obtain ⟨j, hk⟩ := hkind
  obtain ⟨bs, hbs, hbl⟩ := str_of_valid hk hvi
  simp only [Field.bytes, hroff, hlen] at hb
  rw [hbs] at hb ⊢
  rw [hlen] at hbl
  exact ⟨hb, hbl⟩

theorem field_num_decode {s : Schema} (hc : s.Contig) {vals : List FVal} (hv : s.Valid vals)
    (i o l : Nat) (fmt : NumFmt) (hi : i < s.fields.length)
    (hkind : (s.fields.getD i default).desc.kind = .num fmt)
    (hroff : (s.fields.getD i default).roff = o)
    (hlen : (s.fields.getD i default).desc.len = l) :
    ((s.encode vals).drop o).take l = encodeNum {} fmt (numOf (vals.getD i default)) ∧
      decodeNum {} fmt (((s.encode vals).drop o).take l) = some (numOf (vals.getD i default)) ∧
      fmt.Holds {} (numOf (vals.getD i default)) := by
  have hb := Schema.bytes_encode_getD hc hv i hi
  have hvi := Forall2.getD hv i hi
  obtain ⟨n, hn, hvn⟩ := num_of_valid hkind hvi
  simp only [Field.bytes, hroff, hlen] at hb
  rw [hn] at hb ⊢
  obtain ⟨fmt', hk', hd, hd18, hh, -⟩ := hvn
  rw [hkind] at hk'
  cases hk'
  have henc : (s.fields.getD i default).encode (.num n) = encodeNum {} fmt n := by
    unfold Field.encode
    rw [hkind]
  rw [henc] at hb
  refine ⟨hb, ?_, hh⟩
  rw [hb, decodeNum_encodeNum {} fmt n hd hd18 hh]
  rfl

/-! ## 1. `TRNX-RECORD` (`TrnxRecord`, 14 elementary fields, 350 bytes) -/

theorem trnx_length {r : List FVal} (hr : TrnxRecord.Valid r) :
    (TrnxRecord.encode r).length = 350 :=
  Schema.length_encode trnxRecord_contig hr

theorem trnx_fields {r : List FVal} (hr : TrnxRecord.Valid r) :
    tCard (TrnxRecord.encode r) = strOf (r.getD 0 default) ∧
    (strOf (r.getD 0 default)).length = 16 ∧
    tId (TrnxRecord.encode r) = strOf (r.getD 1 default) ∧
    (strOf (r.getD 1 default)).length = 16 ∧
    tDesc (TrnxRecord.encode r) = strOf (r.getD 5 default) ∧
    (strOf (r.getD 5 default)).length = 100 ∧
    tAmt (TrnxRecord.encode r) = numOf (r.getD 6 default) ∧
    AmtOk (TrnxRecord.encode r) := by
  have h0 := field_str_bytes trnxRecord_contig hr 0 0 16 (by decide) ⟨false, rfl⟩ rfl rfl
  have h1 := field_str_bytes trnxRecord_contig hr 1 16 16 (by decide) ⟨false, rfl⟩ rfl rfl
  have h5 := field_str_bytes trnxRecord_contig hr 5 48 100 (by decide) ⟨false, rfl⟩ rfl rfl
  have h6 := (field_num_decode trnxRecord_contig hr 6 148 11
    { digits := 11, scale := 2, signed := true } (by decide) rfl rfl rfl).2.1
  simp only [List.drop_zero] at h0
  have hd : ((tRest (TrnxRecord.encode r)).drop 16).take 100 =
      ((TrnxRecord.encode r).drop 48).take 100 := by
    simp [tRest, List.drop_drop]
  have ha : ((tRest (TrnxRecord.encode r)).drop 116).take 11 =
      ((TrnxRecord.encode r).drop 148).take 11 := by
    simp [tRest, List.drop_drop]
  have hta : tAmt (TrnxRecord.encode r) = numOf (r.getD 6 default) := by
    unfold tAmt
    rw [ha, h6]
    rfl
  refine ⟨h0.1, h0.2, h1.1, h1.2, ?_, h5.2, hta, ?_⟩
  · unfold tDesc; rw [hd, h5.1]
  · unfold AmtOk; rw [ha, hta, h6]

/-! ## 2. `CARD-XREF-RECORD` (`CardXrefRecord`, 4 elementary fields, 50 bytes) -/

theorem xref_length {x : List FVal} (hx : CardXrefRecord.Valid x) :
    (CardXrefRecord.encode x).length = 50 :=
  Schema.length_encode cardXrefRecord_contig hx

theorem xref_fields {x : List FVal} (hx : CardXrefRecord.Valid x) :
    xCard (CardXrefRecord.encode x) = strOf (x.getD 0 default) ∧
    (strOf (x.getD 0 default)).length = 16 ∧
    decodeNum {} { digits := 9 } (((CardXrefRecord.encode x).drop 16).take 9) =
      some (numOf (x.getD 1 default)) ∧
    xCid (CardXrefRecord.encode x) = numOf (x.getD 1 default) ∧
    0 ≤ numOf (x.getD 1 default) ∧ (numOf (x.getD 1 default)).natAbs < 10 ^ 9 ∧
    decodeNum {} { digits := 11 } (((CardXrefRecord.encode x).drop 25).take 11) =
      some (numOf (x.getD 2 default)) ∧
    xAid (CardXrefRecord.encode x) = numOf (x.getD 2 default) ∧
    0 ≤ numOf (x.getD 2 default) ∧ (numOf (x.getD 2 default)).natAbs < 10 ^ 11 := by
  have h0 := field_str_bytes cardXrefRecord_contig hx 0 0 16 (by decide) ⟨false, rfl⟩ rfl rfl
  have h1 := field_num_decode cardXrefRecord_contig hx 1 16 9 { digits := 9 } (by decide) rfl rfl rfl
  have h2 := field_num_decode cardXrefRecord_contig hx 2 25 11 { digits := 11 } (by decide) rfl rfl rfl
  simp only [List.drop_zero] at h0
  have hh1 := (holds_display rfl).mp h1.2.2
  have hh2 := (holds_display rfl).mp h2.2.2
  have hcid : xCid (CardXrefRecord.encode x) = numOf (x.getD 1 default) := by
    unfold xCid; rw [h1.2.1]; rfl
  have haid : xAid (CardXrefRecord.encode x) = numOf (x.getD 2 default) := by
    unfold xAid; rw [h2.2.1]; rfl
  exact ⟨h0.1, h0.2, h1.2.1, hcid, hh1.2 rfl, hh1.1, h2.2.1, haid, hh2.2 rfl, hh2.1⟩

/-! ## 3. `CUSTOMER-RECORD` (`CustomerRecord`, 19 elementary fields, 500 bytes) -/

theorem cust_length {c : List FVal} (hc : CustomerRecord.Valid c) :
    (CustomerRecord.encode c).length = 500 :=
  Schema.length_encode customerRecord_contig hc

theorem encodeNum_unsigned_display {d : Nat} (hd : 0 < d) (v : Int) :
    encodeNum {} { digits := d } v = Sem.digitChars {} d v.natAbs := by
  unfold encodeNum encZoned Sem.digitChars
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [toDigits_succ, Nat.add_sub_cancel, List.map_append, List.map_singleton]

theorem cust_fields {c : List FVal} (hc : CustomerRecord.Valid c) :
    (CustomerRecord.encode c).take 9 = Sem.digitChars {} 9 (numOf (c.getD 0 default)).natAbs ∧
    0 ≤ numOf (c.getD 0 default) ∧ (numOf (c.getD 0 default)).natAbs < 10 ^ 9 ∧
    fld (CustomerRecord.encode c) 9 25 = strOf (c.getD 1 default) ∧
    fld (CustomerRecord.encode c) 34 25 = strOf (c.getD 2 default) ∧
    fld (CustomerRecord.encode c) 59 25 = strOf (c.getD 3 default) ∧
    fld (CustomerRecord.encode c) 84 50 = strOf (c.getD 4 default) ∧
    fld (CustomerRecord.encode c) 134 50 = strOf (c.getD 5 default) ∧
    fld (CustomerRecord.encode c) 184 50 = strOf (c.getD 6 default) ∧
    fld (CustomerRecord.encode c) 234 2 = strOf (c.getD 7 default) ∧
    fld (CustomerRecord.encode c) 236 3 = strOf (c.getD 8 default) ∧
    fld (CustomerRecord.encode c) 239 10 = strOf (c.getD 9 default) ∧
    decodeNum {} { digits := 3 } (((CustomerRecord.encode c).drop 329).take 3) =
      some (numOf (c.getD 17 default)) ∧
    cFico (CustomerRecord.encode c) = numOf (c.getD 17 default) := by
  have h0 := field_num_decode customerRecord_contig hc 0 0 9 { digits := 9 } (by decide) rfl rfl rfl
  have h1 := (field_str_bytes customerRecord_contig hc 1 9 25 (by decide) ⟨false, rfl⟩ rfl rfl).1
  have h2 := (field_str_bytes customerRecord_contig hc 2 34 25 (by decide) ⟨false, rfl⟩ rfl rfl).1
  have h3 := (field_str_bytes customerRecord_contig hc 3 59 25 (by decide) ⟨false, rfl⟩ rfl rfl).1
  have h4 := (field_str_bytes customerRecord_contig hc 4 84 50 (by decide) ⟨false, rfl⟩ rfl rfl).1
  have h5 := (field_str_bytes customerRecord_contig hc 5 134 50 (by decide) ⟨false, rfl⟩ rfl rfl).1
  have h6 := (field_str_bytes customerRecord_contig hc 6 184 50 (by decide) ⟨false, rfl⟩ rfl rfl).1
  have h7 := (field_str_bytes customerRecord_contig hc 7 234 2 (by decide) ⟨false, rfl⟩ rfl rfl).1
  have h8 := (field_str_bytes customerRecord_contig hc 8 236 3 (by decide) ⟨false, rfl⟩ rfl rfl).1
  have h9 := (field_str_bytes customerRecord_contig hc 9 239 10 (by decide) ⟨false, rfl⟩ rfl rfl).1
  have h17 := (field_num_decode customerRecord_contig hc 17 329 3 { digits := 3 } (by decide) rfl rfl rfl).2.1
  simp only [List.drop_zero] at h0
  have h0_dc := h0.1
  rw [encodeNum_unsigned_display (by decide)] at h0_dc
  have hh0 := (holds_display rfl).mp h0.2.2
  have hfico : cFico (CustomerRecord.encode c) = numOf (c.getD 17 default) := by
    unfold cFico; rw [h17]; rfl
  exact ⟨h0_dc, hh0.2 rfl, hh0.1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h17, hfico⟩

/-! ## 4. `ACCOUNT-RECORD` (`AccountRecord`, 13 elementary fields, 300 bytes) -/

theorem acct_length {a : List FVal} (ha : AccountRecord.Valid a) :
    (AccountRecord.encode a).length = 300 :=
  Schema.length_encode accountRecord_contig ha

theorem acct_fields {a : List FVal} (ha : AccountRecord.Valid a) :
    (AccountRecord.encode a).take 11 = Sem.digitChars {} 11 (numOf (a.getD 0 default)).natAbs ∧
    decodeNum {} { digits := 11 } ((AccountRecord.encode a).take 11) =
      some (numOf (a.getD 0 default)) ∧
    aAid (AccountRecord.encode a) = numOf (a.getD 0 default) ∧
    0 ≤ numOf (a.getD 0 default) ∧ (numOf (a.getD 0 default)).natAbs < 10 ^ 11 ∧
    decodeNum {} { digits := 12, scale := 2, signed := true }
      (((AccountRecord.encode a).drop 12).take 12) = some (numOf (a.getD 2 default)) ∧
    aBal (AccountRecord.encode a) = numOf (a.getD 2 default) := by
  have h0 := field_num_decode accountRecord_contig ha 0 0 11 { digits := 11 } (by decide) rfl rfl rfl
  have h2 := (field_num_decode accountRecord_contig ha 2 12 12
    { digits := 12, scale := 2, signed := true } (by decide) rfl rfl rfl).2.1
  simp only [List.drop_zero] at h0
  have h0_dc := h0.1
  rw [encodeNum_unsigned_display (by decide)] at h0_dc
  have hh0 := (holds_display rfl).mp h0.2.2
  have haid : aAid (AccountRecord.encode a) = numOf (a.getD 0 default) := by
    unfold aAid; rw [h0.2.1]; rfl
  have habal : aBal (AccountRecord.encode a) = numOf (a.getD 2 default) := by
    unfold aBal; rw [h2]; rfl
  exact ⟨h0_dc, h0.2.1, haid, hh0.2 rfl, hh0.1, h2, habal⟩

/-! ## 5. Keyed lookup equivalence (`Sem.findKey` ↔ `List.find?`) and `XOk` -/

theorem digitChars_beq {w : Nat} (hd : 0 < w) (hd18 : w ≤ 18) {a b : Int}
    (ha : ({ digits := w } : NumFmt).Holds {} a) (hb : ({ digits := w } : NumFmt).Holds {} b) :
    (Sem.digitChars {} w a.natAbs == Sem.digitChars {} w b.natAbs) = (a == b) := by
  rw [← encodeNum_unsigned_display hd, ← encodeNum_unsigned_display hd]
  exact encodeNum_beq hd hd18 ha hb

theorem cust_key_beq {c : List FVal} (hc : CustomerRecord.Valid c) {cid : Int}
    (hcid : ({ digits := 9 } : NumFmt).Holds {} cid) :
    (Sem.keyOf { off := 0, len := 9 } (CustomerRecord.encode c) ==
      Sem.digitChars {} 9 cid.natAbs) = (numOf (c.getD 0 default) == cid) := by
  have h0 := field_num_decode customerRecord_contig hc 0 0 9 { digits := 9 } (by decide) rfl rfl rfl
  simp only [Sem.keyOf, List.drop_zero] at h0 ⊢
  rw [h0.1, encodeNum_unsigned_display (by decide)]
  exact digitChars_beq (by decide) (by decide) h0.2.2 hcid

theorem acct_key_beq {a : List FVal} (ha : AccountRecord.Valid a) {aid : Int}
    (haid : ({ digits := 11 } : NumFmt).Holds {} aid) :
    (Sem.keyOf { off := 0, len := 11 } (AccountRecord.encode a) ==
      Sem.digitChars {} 11 aid.natAbs) = (numOf (a.getD 0 default) == aid) := by
  have h0 := field_num_decode accountRecord_contig ha 0 0 11 { digits := 11 } (by decide) rfl rfl rfl
  simp only [Sem.keyOf, List.drop_zero] at h0 ⊢
  rw [h0.1, encodeNum_unsigned_display (by decide)]
  exact digitChars_beq (by decide) (by decide) h0.2.2 haid

/-- **Bridge to `XOk`, `custOf`, and `acctOf`**: when `x` is a valid `CardXrefRecord` and
`custs.find?` / `accts.find?` find customer `c` and account `a`, `XOk` holds on
`CardXrefRecord.encode x`, `custOf` = `CustomerRecord.encode c`, and `acctOf` = `AccountRecord.encode a`. -/
theorem xok_of_find {custs accts : List (List FVal)}
    (hcusts : ∀ c ∈ custs, CustomerRecord.Valid c)
    (haccts : ∀ a ∈ accts, AccountRecord.Valid a)
    {x c a : List FVal} (hx : CardXrefRecord.Valid x)
    (hfc : custs.find? (fun c => numOf (c.getD 0 default) == numOf (x.getD 1 default)) = some c)
    (hfa : accts.find? (fun a => numOf (a.getD 0 default) == numOf (x.getD 2 default)) = some a) :
    XOk (custs.map CustomerRecord.encode) (accts.map AccountRecord.encode) (CardXrefRecord.encode x) ∧
    custOf (custs.map CustomerRecord.encode) (CardXrefRecord.encode x) = CustomerRecord.encode c ∧
    acctOf (accts.map AccountRecord.encode) (CardXrefRecord.encode x) = AccountRecord.encode a ∧
    CustomerRecord.Valid c ∧ AccountRecord.Valid a := by
  have hxf := xref_fields hx
  have hcid_holds : ({ digits := 9 } : NumFmt).Holds {} (numOf (x.getD 1 default)) :=
    (field_num_decode cardXrefRecord_contig hx 1 16 9 { digits := 9 } (by decide) rfl rfl rfl).2.2
  have haid_holds : ({ digits := 11 } : NumFmt).Holds {} (numOf (x.getD 2 default)) :=
    (field_num_decode cardXrefRecord_contig hx 2 25 11 { digits := 11 } (by decide) rfl rfl rfl).2.2
  obtain ⟨ic, hfkc, hic, hgetc⟩ := findKey_some
    (fun y hy => cust_key_beq (hcusts y hy) hcid_holds) hfc
  obtain ⟨ia, hfka, hia, hgeta⟩ := findKey_some
    (fun y hy => acct_key_beq (haccts y hy) haid_holds) hfa
  have hcv : CustomerRecord.Valid c := hgetc ▸ hcusts _ (getD_mem_of_lt hic)
  have hav : AccountRecord.Valid a := hgeta ▸ haccts _ (getD_mem_of_lt hia)
  have hcf := cust_fields hcv
  have haf := acct_fields hav
  have hco : custOf (custs.map CustomerRecord.encode) (CardXrefRecord.encode x) =
      CustomerRecord.encode c := by
    unfold custOf
    rw [hxf.2.2.2.1, hfkc, Option.getD_some, ← hgetc]
    exact getD_map_lt CustomerRecord.encode hic
  have hao : acctOf (accts.map AccountRecord.encode) (CardXrefRecord.encode x) =
      AccountRecord.encode a := by
    unfold acctOf
    rw [hxf.2.2.2.2.2.2.2.1, hfka, Option.getD_some, ← hgeta]
    exact getD_map_lt AccountRecord.encode hia
  refine ⟨?_, hco, hao, hcv, hav⟩
  unfold XOk
  rw [hxf.2.2.2.1, hxf.2.2.2.2.2.2.2.1, hfkc, hfka, hco, hao]
  exact ⟨xref_length hx, hxf.2.2.1, hxf.2.2.2.2.2.2.1, rfl, cust_length hcv, rfl, acct_length hav,
    haf.2.1.trans (congrArg some haf.2.2.1.symm),
    haf.2.2.2.2.2.1.trans (congrArg some haf.2.2.2.2.2.2.symm),
    hcf.2.2.2.2.2.2.2.2.2.2.2.2.1.trans (congrArg some hcf.2.2.2.2.2.2.2.2.2.2.2.2.2.symm)⟩

/-- `headS`, `headH`, `headE` expressed directly in terms of the field values of `c` and `a`. -/
theorem head_of_valid {c a : List FVal} (hc : CustomerRecord.Valid c) (ha : AccountRecord.Valid a) :
    headS (CustomerRecord.encode c) (AccountRecord.encode a) =
      stmtHead (stName (strOf (c.getD 1 default)) (strOf (c.getD 2 default)) (strOf (c.getD 3 default)))
        (strOf (c.getD 4 default)) (strOf (c.getD 5 default))
        (stAdd3 (strOf (c.getD 6 default)) (strOf (c.getD 7 default))
          (strOf (c.getD 8 default)) (strOf (c.getD 9 default)))
        (stAcctId (numOf (a.getD 0 default)))
        (edit9 (numOf (a.getD 2 default)))
        (stFico (numOf (c.getD 17 default))) ∧
    headH (CustomerRecord.encode c) (AccountRecord.encode a) =
      htmlHead (stName (strOf (c.getD 1 default)) (strOf (c.getD 2 default)) (strOf (c.getD 3 default)))
        (strOf (c.getD 4 default)) (strOf (c.getD 5 default))
        (stAdd3 (strOf (c.getD 6 default)) (strOf (c.getD 7 default))
          (strOf (c.getD 8 default)) (strOf (c.getD 9 default)))
        (stAcctId (numOf (a.getD 0 default)))
        (edit9 (numOf (a.getD 2 default)))
        (stFico (numOf (c.getD 17 default))) ∧
    headE (CustomerRecord.encode c) (AccountRecord.encode a) =
      headEvents (stName (strOf (c.getD 1 default)) (strOf (c.getD 2 default)) (strOf (c.getD 3 default)))
        (strOf (c.getD 4 default)) (strOf (c.getD 5 default))
        (stAdd3 (strOf (c.getD 6 default)) (strOf (c.getD 7 default))
          (strOf (c.getD 8 default)) (strOf (c.getD 9 default)))
        (stAcctId (numOf (a.getD 0 default)))
        (edit9 (numOf (a.getD 2 default)))
        (stFico (numOf (c.getD 17 default))) := by
  obtain ⟨-, -, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, hfico⟩ := cust_fields hc
  obtain ⟨-, -, haid, -, -, -, habal⟩ := acct_fields ha
  unfold headS headH headE
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, haid, habal, hfico]
  exact ⟨rfl, rfl, rfl⟩

/-- `tranStmtR`, `tranHtmlR`, `tranEvents`, and `addAmt` expressed directly in terms of the field
values of `r`. -/
theorem tran_of_valid {r : List FVal} (hr : TrnxRecord.Valid r) (acc : Int) :
    tranStmtR (TrnxRecord.encode r) =
      tranStmt (strOf (r.getD 1 default)) (strOf (r.getD 5 default)) (editZ (numOf (r.getD 6 default))) ∧
    tranHtmlR (TrnxRecord.encode r) =
      tranHtml (strOf (r.getD 1 default)) (strOf (r.getD 5 default)) (editZ (numOf (r.getD 6 default))) ∧
    tranEvents (TrnxRecord.encode r) =
      .write 1 (tranStmt (strOf (r.getD 1 default)) (strOf (r.getD 5 default)) (editZ (numOf (r.getD 6 default)))) ::
        (tranHtml (strOf (r.getD 1 default)) (strOf (r.getD 5 default)) (editZ (numOf (r.getD 6 default)))).map (.write 2) ∧
    addAmt acc (TrnxRecord.encode r) =
      (Sem.fitNum {} { digits := 11, scale := 2, signed := true, usage := .packed }
        (acc + numOf (r.getD 6 default))).2 := by
  obtain ⟨-, -, hid, -, hdesc, -, hamt, -⟩ := trnx_fields hr
  unfold tranEvents tranStmtR tranHtmlR addAmt
  rw [hid, hdesc, hamt]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Missing customer lookup: `custs.find?` = `none` implies `Sem.findKey` = `none`. -/
theorem cust_findKey_none {custs : List (List FVal)}
    (hcusts : ∀ c ∈ custs, CustomerRecord.Valid c) {x : List FVal} (hx : CardXrefRecord.Valid x)
    (hfc : custs.find? (fun c => numOf (c.getD 0 default) == numOf (x.getD 1 default)) = none) :
    Sem.findKey { off := 0, len := 9 } (Sem.digitChars {} 9 (xCid (CardXrefRecord.encode x)).natAbs)
      (custs.map CustomerRecord.encode) = none := by
  have hxf := xref_fields hx
  have hcid_holds : ({ digits := 9 } : NumFmt).Holds {} (numOf (x.getD 1 default)) :=
    (field_num_decode cardXrefRecord_contig hx 1 16 9 { digits := 9 } (by decide) rfl rfl rfl).2.2
  rw [hxf.2.2.2.1]
  exact findKey_none (fun y hy => cust_key_beq (hcusts y hy) hcid_holds) hfc

/-- Missing account lookup: `accts.find?` = `none` implies `Sem.findKey` = `none`. -/
theorem acct_findKey_none {accts : List (List FVal)}
    (haccts : ∀ a ∈ accts, AccountRecord.Valid a) {x : List FVal} (hx : CardXrefRecord.Valid x)
    (hfa : accts.find? (fun a => numOf (a.getD 0 default) == numOf (x.getD 2 default)) = none) :
    Sem.findKey { off := 0, len := 11 } (Sem.digitChars {} 11 (xAid (CardXrefRecord.encode x)).natAbs)
      (accts.map AccountRecord.encode) = none := by
  have hxf := xref_fields hx
  have haid_holds : ({ digits := 11 } : NumFmt).Holds {} (numOf (x.getD 2 default)) :=
    (field_num_decode cardXrefRecord_contig hx 2 25 11 { digits := 11 } (by decide) rfl rfl rfl).2.2
  rw [hxf.2.2.2.2.2.2.2.1]
  exact findKey_none (fun y hy => acct_key_beq (haccts y hy) haid_holds) hfa

#print axioms trnx_fields
#print axioms xref_fields
#print axioms cust_fields
#print axioms acct_fields
#print axioms xok_of_find
#print axioms head_of_valid
#print axioms tran_of_valid
#print axioms cust_findKey_none
#print axioms acct_findKey_none

end EquivLean.Modernize.Cbstm03a.StmBridge
