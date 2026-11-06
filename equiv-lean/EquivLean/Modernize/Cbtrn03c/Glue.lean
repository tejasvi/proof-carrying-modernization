import EquivLean.Modernize.Cbtrn03c.Model
import EquivLean.Modernize.Cbtrn03c.Domain
import EquivLean.Demo.Cobol.Cbtrn03c.Every
import EquivLean.Modernize.GlueKit

/-!
# CBTRN03C: coblean's model and the translations' model

coblean's `cbtrn03c_every` describes the COBOL run of CBTRN03C for every input given as coblean's
structures (`Tran`, `Xref`, the type and category records as bytes, the date parameter record),
by its model: a fold over the transactions (`step3x`: the date test, the lookups, then `step3`'s
report lines) from `init3 x0`, and the end of the run (`result3`).  `Model.run` is what the
translations do on field values (`loop`, `tranStep`, `report`, `eofTail`).

* `toTran`, `toXref` build coblean's records from the field values of the statements' records;
  the type and category records are the records' bytes; the date parameter record is the record
  padded to the file's 80 bytes (`parmOf`), as the statements give it.
* The report lines: coblean's bytes, as code points, are `Model`'s lines (`nameLine_text`,
  `pageLine_text`, `detailLine_text`, …); the amounts' numeric editing `-ZZZ,ZZZ,ZZZ.ZZ` /
  `+ZZZ,ZZZ,ZZZ.ZZ` is `editAmt` for every value (`edit_text`, by the position of the first
  non-zero digit, `gen_amt`).
* The keyed READs find the translations' first matches, and fail exactly when the translations'
  searches fail (`xrefOf_eq`, `typeDesc_eq`, `catDesc_eq`, `xref_none`, `type_none`, `cat_none`).
* The proof is a simulation, one transaction at a time (`loop_corr`): a transaction in the date
  range whose lookups succeed keeps `Corr` (`step_corr`: the card, the first-detail flag, the line
  counter modulo the size of `WS-LINE-COUNTER`, the totals, the account id, the dates of the name
  header, the outputs); a date out of range ends the report on both sides; a failed lookup abends
  on both sides with the same outputs (`OutCorr`, `abend_corr`).
* `cobol_outputs`: with coblean's theorem, the COBOL run of the statements ends with GOBACK or
  abends with code 999, as `Model.run`'s `abended` says, and its displays and the report lines it
  writes (decoded) are `Model.run`'s.  The harness storage holds `tran0` in the record area and a
  zero account id (`initMem_tran0`, `initMem_xacct`).
-/

open Cobol EquivLean.Cobol.Rec EquivLean.Modernize.Cbtrn03c.Model
open Cobol.Digits (toDigits)
open CardDemo.Cbtrn03c (Tran Xref)
open EquivLean.Modernize.GlueKit

namespace EquivLean.Modernize.Cbtrn03c.Glue

/-! ## The amounts: numeric editing -/

/-- The positions of `ZZZ,ZZZ,ZZZ.ZZ` (after the sign). -/
def amtPs : List Edit.Pos :=
  [.digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
    .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
    .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)]

theorem amtPat : "ZZZ,ZZZ,ZZZ".toList = ['Z', 'Z', 'Z', ',', 'Z', 'Z', 'Z', ',', 'Z', 'Z', 'Z'] := by
  decide +kernel

theorem cp_space : cp037Code ({} : Config).space = 32 := by decide +kernel
theorem cp_comma : cp037Code (Edit.symChar {} .comma) = 44 := by decide +kernel
theorem cp_dot : cp037Code (Edit.symChar {} .dot) = 46 := by decide +kernel

/-- One case of `gen_amt`: the digits are known up to the first non-zero one. -/
macro "amt_leaf" : tactic =>
  `(tactic| simp [Edit.editOpt.gen, zzz, List.findIdx?_cons, cp037Code_digitByte, cp_space,
    cp_comma, cp_dot, *])

/-- The digits and insertion characters of `ZZZ,ZZZ,ZZZ.ZZ`: the leading zeros of the integer
part suppressed (with the commas among them), as `zzz` does. -/
theorem gen_amt (a0 a1 a2 a3 a4 a5 a6 a7 a8 b9 b10 : Nat) (h0 : a0 < 10) (h1 : a1 < 10)
    (h2 : a2 < 10) (h3 : a3 < 10) (h4 : a4 < 10) (h5 : a5 < 10) (h6 : a6 < 10) (h7 : a7 < 10)
    (h8 : a8 < 10) (h9 : b9 < 10) (h10 : b10 < 10) (neg : Bool) :
    ((Edit.editOpt.gen {} 9 [a0, a1, a2, a3, a4, a5, a6, a7, a8, b9, b10] neg (some .z)
      (min 9 ((List.findIdx? (fun x => x != 0) [a0, a1, a2, a3, a4, a5, a6, a7, a8, b9, b10]).getD 11))
      0 [.digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
        .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
        .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)]).map
      (·.1)).map cp037Code =
    zzz ['Z', 'Z', 'Z', ',', 'Z', 'Z', 'Z', ',', 'Z', 'Z', 'Z'] [a0, a1, a2, a3, a4, a5, a6, a7, a8] true ++
      [46, 48 + b9, 48 + b10] := by
  by_cases e0 : a0 = 0
  · subst e0
    by_cases e1 : a1 = 0
    · subst e1
      by_cases e2 : a2 = 0
      · subst e2
        by_cases e3 : a3 = 0
        · subst e3
          by_cases e4 : a4 = 0
          · subst e4
            by_cases e5 : a5 = 0
            · subst e5
              by_cases e6 : a6 = 0
              · subst e6
                by_cases e7 : a7 = 0
                · subst e7
                  by_cases e8 : a8 = 0
                  · subst e8
                    by_cases e9 : b9 = 0 <;> by_cases e10 : b10 = 0 <;> amt_leaf
                  · amt_leaf
                · amt_leaf
              · amt_leaf
            · amt_leaf
          · amt_leaf
        · amt_leaf
      · amt_leaf
    · amt_leaf
  · amt_leaf

theorem toDigits_11 (m : Nat) :
    toDigits 10 11 m = toDigits 10 9 (m / 100) ++ [m % 100 / 10, m % 10] := by
  show toDigits 10 9 (m / 10 / 10) ++ [m / 10 % 10] ++ [m % 10] = _
  rw [Nat.div_div_eq_div_mul]
  simp only [List.append_assoc, List.singleton_append]
  congr 3
  omega

/-- The picture `-ZZZ,ZZZ,ZZZ.ZZ` (`plus` false) or `+ZZZ,ZZZ,ZZZ.ZZ` (`plus` true). -/
def amtPic (plus : Bool) : List ESym :=
  [if plus then .plus else .minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z]

theorem cp_sign (plus neg : Bool) :
    (Edit.fixedBytes {} (if plus then .plus else .minus) neg).map cp037Code =
      [if neg then 45 else if plus then 43 else 32] := by
  cases plus <;> cases neg <;> decide +kernel

/-- **The amounts of the report**: coblean's editing by `-ZZZ,ZZZ,ZZZ.ZZ` / `+ZZZ,ZZZ,ZZZ.ZZ`, as
code points, is `editAmt`. -/
theorem edit_text (plus : Bool) (v : Int) :
    ((Edit.edit {} (amtPic plus) false v 2).getD []).map cp037Code = editAmt v plus := by
  have hc : Edit.classify (amtPic plus) = some (.fixed (if plus then .plus else .minus) :: amtPs) := by
    cases plus <;> decide
  have hf : Edit.floatBeforePoint (.fixed (if plus then .plus else .minus) :: amtPs) = true := by
    cases plus <;> decide
  have hfs : Edit.floatSym (amtPic plus) = none := by cases plus <;> decide
  have hw : Edit.picWidth (amtPic plus) = 15 := by cases plus <;> decide
  unfold Edit.edit Edit.editOpt
  simp only [hc, Option.bind_eq_bind, Option.bind_some, hf, hfs, hw, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  simp [Edit.numDigitPos, Edit.fracDigits, amtPs, rescale]
  have h11 : (List.findIdx? (fun x => x == Edit.Pos.digit none)
      [Edit.Pos.digit (some ESym.z), Edit.Pos.digit (some ESym.z), Edit.Pos.digit (some ESym.z),
        Edit.Pos.digit (some ESym.z), Edit.Pos.digit (some ESym.z), Edit.Pos.digit (some ESym.z),
        Edit.Pos.digit (some ESym.z), Edit.Pos.digit (some ESym.z), Edit.Pos.digit (some ESym.z),
        Edit.Pos.digit (some ESym.z), Edit.Pos.digit (some ESym.z)]).getD 11 = 11 := by decide
  have hmin : ∀ z, min 9 (min 11 z) = min 9 z := by intro z; omega
  rw [h11, hmin]
  unfold editAmt
  generalize v.natAbs % 100000000000 = m
  by_cases hm : m = 0
  · subst hm
    simp [cp_space]
  · simp only [hm, ↓reduceIte, Option.getD_some, toDigits_11]
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, hA⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8,
        toDigits 10 9 (m / 100) = [a0, a1, a2, a3, a4, a5, a6, a7, a8] :=
      ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    have hlt := Cobol.Digits.toDigits_lt (b := 10) (by decide) 9 (m / 100)
    rw [hA] at hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hlt
    rw [hA, amtPat]
    show List.map cp037Code (List.map (fun x => x.fst)
      ((Edit.fixedBytes {} (if plus = true then ESym.plus else ESym.minus) (decide (v < 0))).map
        (·, false) ++ _)) = _
    rw [List.map_append, List.map_append, List.map_map, List.map_map]
    have hs := cp_sign plus (decide (v < 0))
    simp only [Function.comp_def] at hs ⊢
    simp only [List.cons_append, List.nil_append]
    rw [hs, gen_amt a0 a1 a2 a3 a4 a5 a6 a7 a8 (m % 100 / 10) (m % 10) h0 h1 h2 h3 h4 h5 h6 h7 h8
      (by omega) (by omega)]
    simp


theorem editMinus_text (v : Int) :
    (CardDemo.Cbtrn03c.editMinus v).map cp037Code = editAmt v false := edit_text false v
theorem editPlus_text (v : Int) :
    (CardDemo.Cbtrn03c.editPlus v).map cp037Code = editAmt v true := edit_text true v

theorem length_editAmt (v : Int) (plus : Bool) : (editAmt v plus).length = 15 := by
  rw [← edit_text plus v, List.length_map]
  cases plus
  · exact CardDemo.Cbtrn03c.editMinus_length v
  · exact CardDemo.Cbtrn03c.editPlus_length v

/-! ## The report lines -/

theorem pad_of_length {s : List Nat} {w : Nat} (h : s.length = w) : pad s w = s := by
  subst h; simp [pad]

theorem to133_of_length {l : List Nat} (h : l.length ≤ 133) :
    to133 l = l ++ List.replicate (133 - l.length) 32 := by
  simp [to133, pad, List.take_of_length_le h]

theorem cps_append (a b : List UInt8) : cps (a ++ b) = cps a ++ cps b := List.map_append ..
theorem length_cps (a : List UInt8) : (cps a).length = a.length := List.length_map ..

theorem cp_64 : cp037Code 64 = 32 := by decide +kernel
theorem cp_96 : cp037Code 96 = 45 := by decide +kernel
theorem cp_75 : cp037Code 75 = 46 := by decide +kernel

theorem nameHead_text : CardDemo.Cbtrn03c.nameHead.map cp037Code =
    pad (txt "DALYREPT") 38 ++ pad (txt "Daily Transaction Report") 41 ++ pad (txt "Date Range: ") 12 := by
  decide +kernel
theorem toMsg_text : CardDemo.Cbtrn03c.toMsg.map cp037Code = txt " to " := by decide +kernel
theorem hdr1_text : CardDemo.Cbtrn03c.hdr1Line.map cp037Code = header1 := by decide +kernel
theorem pageHead_text : CardDemo.Cbtrn03c.pageHead.map cp037Code =
    pad (txt "Page Total") 11 ++ List.replicate 86 46 := by decide +kernel
theorem acctHead_text : CardDemo.Cbtrn03c.acctHead.map cp037Code =
    pad (txt "Account Total") 13 ++ List.replicate 84 46 := by decide +kernel
theorem grandHead_text : CardDemo.Cbtrn03c.grandHead.map cp037Code =
    pad (txt "Grand Total") 11 ++ List.replicate 86 46 := by decide +kernel

theorem blankLine_text : CardDemo.Cbtrn03c.blankLine.map cp037Code = blankLine := by
  simp [CardDemo.Cbtrn03c.blankLine, blankLine, cp_64]

theorem hdr2_text : CardDemo.Cbtrn03c.hdr2Line.map cp037Code = header2 := by
  simp [CardDemo.Cbtrn03c.hdr2Line, header2, cp_96]

/-- The report name header with the dates `s` … `e` (10 characters each). -/
theorem nameLine_text {s e : List UInt8} (hs : s.length = 10) (he : e.length = 10) :
    (CardDemo.Cbtrn03c.nameLine s e).map cp037Code = nameHeader (cps s) (cps e) := by
  have hn : (pad (txt "DALYREPT") 38 ++ pad (txt "Daily Transaction Report") 41 ++
      pad (txt "Date Range: ") 12).length = 91 := by decide +kernel
  have ht : (txt " to ").length = 4 := by decide +kernel
  unfold CardDemo.Cbtrn03c.nameLine nameHeader
  rw [to133_of_length (by simp only [List.length_append, hn, length_cps, hs, he, ht]; omega)]
  simp only [List.map_append, nameHead_text, toMsg_text, List.map_replicate, cp_64,
    List.length_append, length_cps, hs, he, ht, List.append_assoc]
  rfl

theorem pageLine_text (v : Int) :
    (CardDemo.Cbtrn03c.pageLine v).map cp037Code = pageTotalLine v := by
  unfold CardDemo.Cbtrn03c.pageLine pageTotalLine
  have hp : (pad (txt "Page Total") 11 ++ List.replicate 86 46).length = 97 := by decide +kernel
  rw [to133_of_length (by simp only [List.length_append, hp, length_editAmt]; omega)]
  simp only [List.map_append, pageHead_text, editPlus_text, List.map_replicate, cp_64,
    List.length_append, length_editAmt, List.append_assoc]
  rfl

theorem acctLine_text (v : Int) :
    (CardDemo.Cbtrn03c.acctLine v).map cp037Code = acctTotalLine v := by
  unfold CardDemo.Cbtrn03c.acctLine acctTotalLine
  have hp : (pad (txt "Account Total") 13 ++ List.replicate 84 46).length = 97 := by decide +kernel
  rw [to133_of_length (by simp only [List.length_append, hp, length_editAmt]; omega)]
  simp only [List.map_append, acctHead_text, editPlus_text, List.map_replicate, cp_64,
    List.length_append, length_editAmt, List.append_assoc]
  rfl

theorem grandLine_text (v : Int) :
    (CardDemo.Cbtrn03c.grandLine v).map cp037Code = grandTotalLine v := by
  unfold CardDemo.Cbtrn03c.grandLine grandTotalLine
  have hp : (pad (txt "Grand Total") 11 ++ List.replicate 86 46).length = 97 := by decide +kernel
  rw [to133_of_length (by simp only [List.length_append, hp, length_editAmt]; omega)]
  simp only [List.map_append, grandHead_text, editPlus_text, List.map_replicate, cp_64,
    List.length_append, length_editAmt, List.append_assoc]
  rfl

/-! ## The input records as coblean's structures -/

/-- coblean's transaction of a record's field values (the merchant fields as their bytes). -/
def toTran (t : List FVal) : Tran :=
  ⟨tId t, tType t, tCat t, tSource t, strOf (t.getD 4 default), tAmt t,
    encodeNum {} CardDemo.Cbtrn03c.TRAN_MERCHANT_ID.fmt (numOf (t.getD 6 default)) ++
      strOf (t.getD 7 default) ++ strOf (t.getD 8 default) ++ strOf (t.getD 9 default),
    tCard t, strOf (t.getD 11 default), strOf (t.getD 12 default), strOf (t.getD 13 default)⟩

/-- coblean's card cross-reference of a record's field values (the customer id as its bytes). -/
def toXref (x : List FVal) : Xref :=
  ⟨xCard x, encodeNum {} CardDemo.Cbtrn03c.XREF_CUST_ID.fmt (numOf (x.getD 1 default)), xAcct x,
    strOf (x.getD 3 default)⟩

theorem tran_shape {t : List FVal} (ht : TranRecord.Valid t) :
    ∃ id ty cat src desc amt merch mname mcity mzip card orig proc fill,
      t = [.str id, .str ty, .num cat, .str src, .str desc, .num amt, .num merch, .str mname,
        .str mcity, .str mzip, .str card, .str orig, .str proc, .str fill] ∧
      id.length = 16 ∧ ty.length = 2 ∧ cat.natAbs < 10000 ∧ 0 ≤ cat ∧ src.length = 10 ∧
      desc.length = 100 ∧ amt.natAbs < 100000000000 ∧ merch.natAbs < 1000000000 ∧ 0 ≤ merch ∧
      mname.length = 50 ∧ mcity.length = 50 ∧ mzip.length = 10 ∧ card.length = 16 ∧
      orig.length = 26 ∧ proc.length = 26 ∧ fill.length = 20 := by
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
    simp_all

theorem toTran_valid {t : List FVal} (ht : TranRecord.Valid t) : (toTran t).valid := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, h1, h2,
    h3, h4, h5, h6, h7, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := tran_shape ht
  have hm : (encodeNum {} CardDemo.Cbtrn03c.TRAN_MERCHANT_ID.fmt merch).length = 9 :=
    (length_encodeNum {} CardDemo.Cbtrn03c.TRAN_MERCHANT_ID.fmt _ (by decide)).trans rfl
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h13, h14, h15, h16⟩
  simp [toTran, strOf, numOf, hm, h10, h11, h12]

theorem toTran_bytes {t : List FVal} (ht : TranRecord.Valid t) :
    (toTran t).bytes = TranRecord.encode t := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, -⟩ :=
    tran_shape ht
  have e : TranRecord.encode [.str id, .str ty, .num cat, .str src, .str desc, .num amt,
      .num merch, .str mname, .str mcity, .str mzip, .str card, .str orig, .str proc, .str fill] =
      id ++ (ty ++ (encodeNum {} ({ digits := 4 } : NumFmt) cat ++ (src ++ (desc ++
      (encodeNum {} CardDemo.Cbtrn03c.TRAN_AMT.fmt amt ++
      (encodeNum {} CardDemo.Cbtrn03c.TRAN_MERCHANT_ID.fmt merch ++ (mname ++ (mcity ++
      (mzip ++ (card ++ (orig ++ (proc ++ (fill ++ []))))))))))))) := rfl
  rw [e]
  simp [Tran.bytes, toTran, tId, tType, tCat, tSource, tAmt, tCard, strOf, numOf,
    List.append_assoc]

/-- A transaction's DISPLAY line. -/
theorem tran_text {t : List FVal} (ht : TranRecord.Valid t) :
    TranRecord.textS t = (toTran t).bytes.map cp037Code := by
  rw [Schema.textS_eq (by decide) ht, toTran_bytes ht]

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

theorem toXref_valid {x : List FVal} (hx : CardXrefRecord.Valid x) : (toXref x).valid := by
  obtain ⟨card, cust, acct, fill, rfl, h1, -, -, h4, h5, h6⟩ := xref_shape hx
  have hc : (encodeNum {} CardDemo.Cbtrn03c.XREF_CUST_ID.fmt cust).length = 9 :=
    (length_encodeNum {} CardDemo.Cbtrn03c.XREF_CUST_ID.fmt _ (by decide)).trans rfl
  exact ⟨h1, hc, h4, h5, h6⟩

theorem toXref_bytes {x : List FVal} (hx : CardXrefRecord.Valid x) :
    (toXref x).bytes = CardXrefRecord.encode x := by
  obtain ⟨card, cust, acct, fill, rfl, -⟩ := xref_shape hx
  have e : CardXrefRecord.encode [.str card, .num cust, .num acct, .str fill] =
      card ++ (encodeNum {} CardDemo.Cbtrn03c.XREF_CUST_ID.fmt cust ++
        (encodeNum {} CardDemo.Cbtrn03c.XREF_ACCT_ID.fmt acct ++ (fill ++ []))) := rfl
  rw [e]
  simp [Xref.bytes, toXref, xCard, xAcct, strOf, numOf, List.append_assoc]

/-! ## The detail line -/

theorem digitChars_text (w n : Nat) : (Sem.digitChars {} w n).map cp037Code = zpad w n := by
  unfold Sem.digitChars zpad
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  exact cp037Code_digitByte d (Cobol.Digits.toDigits_lt (by decide) w n d hd)

/-- The detail line of a transaction, its account id, type and category descriptions. -/
theorem detailLine_text {T X Y C : List FVal} (hT : TranRecord.Valid T)
    (hY : (yDesc Y).length = 50) (hC : (cDesc C).length = 50) :
    (CardDemo.Cbtrn03c.detailLine (toTran T) (xAcct X) ((yDesc Y).take 15)
      ((cDesc C).take 29)).map cp037Code = detailLine T X Y C := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, h1, h2,
    -, -, h5, -⟩ := tran_shape hT
  have hy15 : (cps ((yDesc Y).take 15)).length = 15 := by simp [cps, hY]
  have hc29 : (cps ((cDesc C).take 29)).length = 29 := by simp [cps, hC]
  have hcat : ∀ c, (encodeNum {} CardDemo.Cbtrn03c.TRAN_REPORT_CAT_CD.fmt c).map cp037Code =
      digs 4 c := fun c => text_unsigned rfl rfl (by decide) c
  have hlen : (cps (tId [.str id, .str ty, .num cat, .str src, .str desc, .num amt, .num merch,
      .str mname, .str mcity, .str mzip, .str card, .str orig, .str proc, .str fill])).length = 16 ∧
      (cps (tType [.str id, .str ty, .num cat, .str src, .str desc, .num amt, .num merch,
      .str mname, .str mcity, .str mzip, .str card, .str orig, .str proc, .str fill])).length = 2 ∧
      (cps (tSource [.str id, .str ty, .num cat, .str src, .str desc, .num amt, .num merch,
      .str mname, .str mcity, .str mzip, .str card, .str orig, .str proc, .str fill])).length = 10 := by
    simp [cps, tId, tType, tSource, strOf, h1, h2, h5]
  unfold CardDemo.Cbtrn03c.detailLine detailLine
  rw [pad_of_length hy15, pad_of_length hc29]
  rw [to133_of_length (by simp [hlen, digs, zpad, hy15, hc29, length_editAmt])]
  simp only [List.map_append, digitChars_text, hcat, editMinus_text, List.map_replicate, cp_64,
    cp_96, List.map_cons, List.map_nil]
  simp [digs, zpad, length_editAmt, toTran, tId, tType, tSource, tAmt, tCat,
    cps, List.append_assoc, strOf, h1, h2, h5, hY, hC]
/-! ## The keyed lookups -/

/-- coblean's cross-reference lookup finds the translations' first match. -/
theorem xrefOf_eq {xs : List (List FVal)} (hxs : ∀ x ∈ xs, CardXrefRecord.Valid x)
    {card : List UInt8} {X : List FVal} (hX : xs.find? (fun x => xCard x == card) = some X) :
    CardDemo.Cbtrn03c.xrefOf (xs.map toXref) card = toXref X := by
  have hp : ∀ x ∈ xs.map toXref, (Sem.keyOf { off := 0, len := 16 } x.bytes == card) =
      (x.card == card) := by
    intro x hx
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx
    obtain ⟨c, cu, a, f, rfl, hc, -⟩ := xref_shape (hxs x0 hx0)
    simp only [Sem.keyOf, List.drop_zero, Xref.bytes, toXref, xCard, strOf, List.append_assoc,
      List.getD_cons_zero]
    rw [List.take_left' hc]
  have hf : (xs.map toXref).find? (fun x => x.card == card) = some (toXref X) := by
    rw [List.find?_map]
    simp only [Function.comp_def]
    rw [show (fun x => (toXref x).card == card) = (fun x => xCard x == card) from rfl, hX]
    rfl
  obtain ⟨i, hi, -, hiX⟩ := findKey_some hp hf
  unfold CardDemo.Cbtrn03c.xrefOf
  rw [hi, Option.getD_some, hiX]

theorem type_shape {y : List FVal} (hy : TranTypeRecord.Valid y) :
    ∃ ty desc fill, y = [.str ty, .str desc, .str fill] ∧ ty.length = 2 ∧ desc.length = 50 ∧
      fill.length = 8 := by
  have hl : y.length = 3 := hy.length_eq.symm
  match y, hl, hy with
  | [x0, x1, x2], _, .cons h0 (.cons h1 (.cons h2 .nil)) =>
    obtain ⟨ty, rfl, hty⟩ := str_of_valid rfl h0
    obtain ⟨desc, rfl, hdesc⟩ := str_of_valid rfl h1
    obtain ⟨fill, rfl, hfill⟩ := str_of_valid rfl h2
    exact ⟨ty, desc, fill, rfl, hty, hdesc, hfill⟩

/-- coblean's transaction type lookup gives the translations' description (15 characters). -/
theorem typeDesc_eq {ys : List (List FVal)} (hys : ∀ y ∈ ys, TranTypeRecord.Valid y)
    {ty : List UInt8} {Y : List FVal} (hY : ys.find? (fun y => yType y == ty) = some Y) :
    CardDemo.Cbtrn03c.typeDesc (ys.map TranTypeRecord.encode) ty = (yDesc Y).take 15 := by
  have hp : ∀ y ∈ ys, (Sem.keyOf { off := 0, len := 2 } (TranTypeRecord.encode y) == ty) =
      (yType y == ty) := by
    intro y hy
    obtain ⟨t, d, f, rfl, ht, -⟩ := type_shape (hys y hy)
    show (Sem.keyOf { off := 0, len := 2 } (t ++ (d ++ (f ++ []))) == ty) = _
    simp only [Sem.keyOf, List.drop_zero, List.take_left' ht, yType, strOf, List.getD_cons_zero]
  obtain ⟨i, hi, -, hiY⟩ := findKey_some hp hY
  have hYm : Y ∈ ys := List.mem_of_find?_eq_some hY
  obtain ⟨t, d, f, rfl, ht, hd, -⟩ := type_shape (hys _ hYm)
  have hg : (ys.map TranTypeRecord.encode).getD i [] = t ++ (d ++ (f ++ [])) := by
    have hi' : i < ys.length := by simpa using findKey_lt' hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi']
    simp only [Option.map_some, Option.getD_some]
    have := hiY
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] at this
    simp only [Option.getD_some] at this
    rw [this]
    rfl
  simp only [CardDemo.Cbtrn03c.typeDesc, hi, Option.getD_some, hg, yDesc, strOf,
    List.getD_cons_succ, List.getD_cons_zero]
  rw [List.drop_left' ht]
  simp [List.take_append, hd]

theorem catg_shape {c : List FVal} (hc : TranCatRecord.Valid c) :
    ∃ ty cat desc fill, c = [.str ty, .num cat, .str desc, .str fill] ∧ ty.length = 2 ∧
      cat.natAbs < 10000 ∧ 0 ≤ cat ∧ desc.length = 50 ∧ fill.length = 4 := by
  have hl : c.length = 4 := hc.length_eq.symm
  match c, hl, hc with
  | [x0, x1, x2, x3], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))) =>
    obtain ⟨ty, rfl, hty⟩ := str_of_valid rfl h0
    obtain ⟨cat, rfl, hcat⟩ := num_of_valid rfl h1
    obtain ⟨desc, rfl, hdesc⟩ := str_of_valid rfl h2
    obtain ⟨fill, rfl, hfill⟩ := str_of_valid rfl h3
    obtain ⟨_, k1, -, -, n1, -⟩ := hcat
    cases k1
    rw [holds_display rfl] at n1
    refine ⟨ty, cat, desc, fill, rfl, ?_⟩
    simp_all

/-- coblean's category lookup gives the translations' description (29 characters). -/
theorem catDesc_eq {cs : List (List FVal)} (hcs : ∀ c ∈ cs, TranCatRecord.Valid c)
    {ty : List UInt8} {cat : Int} (hty : ty.length = 2) (hcat0 : 0 ≤ cat)
    (hcat : cat.natAbs < 10000) {C : List FVal}
    (hC : cs.find? (fun c => cType c == ty && cCat c == cat) = some C) :
    CardDemo.Cbtrn03c.catDesc (cs.map TranCatRecord.encode) ty cat = (cDesc C).take 29 := by
  have henc : ∀ c, (encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt c).length = 4 := fun c =>
    (length_encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt c (by decide)).trans rfl
  have hp : ∀ c ∈ cs, (Sem.keyOf { off := 0, len := 6 } (TranCatRecord.encode c) ==
      ty ++ encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt cat) =
      (cType c == ty && cCat c == cat) := by
    intro c hc
    obtain ⟨t, k, d, f, rfl, ht, hk, hk0, -⟩ := catg_shape (hcs c hc)
    show (Sem.keyOf { off := 0, len := 6 }
      (t ++ (encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt k ++ (d ++ (f ++ [])))) == _) = _
    have hkey : Sem.keyOf { off := 0, len := 6 }
        (t ++ (encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt k ++ (d ++ (f ++ [])))) =
        t ++ encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt k := by
      simp only [Sem.keyOf, List.drop_zero]
      rw [← List.append_assoc]
      exact List.take_left' (by simp [ht, henc])
    rw [hkey]
    simp only [cType, cCat, strOf, numOf, List.getD_cons_zero, List.getD_cons_succ]
    have hb := encodeNum_beq (f := CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt) (by decide) (by decide)
      ((holds_display rfl).2 ⟨hk, fun _ => hk0⟩) ((holds_display rfl).2 ⟨hcat, fun _ => hcat0⟩)
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, Bool.and_eq_true]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj h (by rw [ht, hty])
      refine ⟨h1, ?_⟩
      have := hb
      rw [h2, beq_self_eq_true] at this
      exact (beq_iff_eq.1 this.symm)
    · rintro ⟨rfl, rfl⟩; rfl
  obtain ⟨i, hi, -, hiC⟩ := findKey_some hp hC
  have hCm : C ∈ cs := List.mem_of_find?_eq_some hC
  obtain ⟨t, k, d, f, rfl, ht, -, -, hd, -⟩ := catg_shape (hcs _ hCm)
  have hi' : i < cs.length := by simpa using findKey_lt' hi
  have hg : (cs.map TranCatRecord.encode).getD i [] =
      t ++ (encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt k ++ (d ++ (f ++ []))) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi']
    simp only [Option.map_some, Option.getD_some]
    have := hiC
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] at this
    simp only [Option.getD_some] at this
    rw [this]
    rfl
  simp only [CardDemo.Cbtrn03c.catDesc, hi, Option.getD_some, hg, cDesc, strOf,
    List.getD_cons_succ, List.getD_cons_zero]
  rw [← List.append_assoc, List.drop_left' (by simp [ht, henc])]
  simp [List.take_append, hd]

/-! ### The report lines, as `cps` -/

theorem tran_cps {t : List FVal} (ht : TranRecord.Valid t) :
    TranRecord.textS t = cps (toTran t).bytes := tran_text ht
theorem pageLine_cps (v : Int) : cps (CardDemo.Cbtrn03c.pageLine v) = pageTotalLine v :=
  pageLine_text v
theorem acctLine_cps (v : Int) : cps (CardDemo.Cbtrn03c.acctLine v) = acctTotalLine v :=
  acctLine_text v
theorem grandLine_cps (v : Int) : cps (CardDemo.Cbtrn03c.grandLine v) = grandTotalLine v :=
  grandLine_text v
theorem hdr1_cps : cps CardDemo.Cbtrn03c.hdr1Line = header1 := hdr1_text
theorem hdr2_cps : cps CardDemo.Cbtrn03c.hdr2Line = header2 := hdr2_text
theorem blank_cps : cps CardDemo.Cbtrn03c.blankLine = blankLine := blankLine_text
theorem nameLine_cps {s e : List UInt8} (hs : s.length = 10) (he : e.length = 10) :
    cps (CardDemo.Cbtrn03c.nameLine s e) = nameHeader (cps s) (cps e) := nameLine_text hs he

/-! ## The simulation (the transactions of the report) -/

theorem length_to133 (l : List Nat) : (to133 l).length = 133 := by
  simp [to133, pad]; omega

theorem length_lines : blankLine.length = 133 ∧ header1.length = 133 ∧ header2.length = 133 ∧
    (∀ rs re, (nameHeader rs re).length = 133) ∧ (∀ v, (pageTotalLine v).length = 133) ∧
    (∀ v, (acctTotalLine v).length = 133) ∧ (∀ v, (grandTotalLine v).length = 133) ∧
    (∀ t x y c, (detailLine t x y c).length = 133) := by
  refine ⟨by simp [blankLine], length_to133 _, by simp [header2], fun _ _ => length_to133 _,
    fun _ => length_to133 _, fun _ => length_to133 _, fun _ => length_to133 _,
    fun _ _ _ _ => length_to133 _⟩

theorem wlen_append {xs ys : List (List Nat)} (h1 : ∀ l ∈ xs, l.length = 133)
    (h2 : ∀ l ∈ ys, l.length = 133) : ∀ l ∈ xs ++ ys, l.length = 133 := by
  intro l hl
  rcases List.mem_append.1 hl with h | h
  · exact h1 l h
  · exact h2 l h

theorem wlen_cons {x : List Nat} {xs : List (List Nat)} (h1 : x.length = 133)
    (h2 : ∀ l ∈ xs, l.length = 133) : ∀ l ∈ x :: xs, l.length = 133 := by
  intro l hl
  rcases List.mem_cons.1 hl with rfl | h
  · exact h1
  · exact h2 l h

theorem wlen_nil : ∀ l ∈ ([] : List (List Nat)), l.length = 133 := by simp

/-- The translations' state `S` after the same transactions as coblean's report state `M`
(date parameters `d`): the same card, first-detail flag, line counter (modulo the size of
`WS-LINE-COUNTER`), totals and account id; the dates of the name header once the first detail
is written; the outputs of `M`'s events. -/
structure Corr (d : List FVal) (S : St) (M : CardDemo.Cbtrn03c.M3) : Prop where
  card : S.card = M.card
  first : S.first = M.first
  lc : S.lc = M.lines % 1000000000
  page : S.page = M.page
  acct : S.acct = M.acct
  grand : S.grand = M.grand
  xacct : xAcct S.xref = M.xacct
  dates : S.first = false → S.rs = cps (dStart d) ∧ S.re = cps (dEnd d)
  disp : S.disp = txt "START OF EXECUTION OF PROGRAM CBTRN03C" ::
    (txt "Reporting from " ++ cps (dStart d) ++ txt " to " ++ cps (dEnd d)) ::
    (dispL M.out.reverse).map cps
  writes : S.writes = (wrL 5 M.out.reverse).map cps
  wlen : ∀ l ∈ S.writes, l.length = 133

theorem trunc11_eq (v : Int) : trunc11 v = CardDemo.Cbtrn03c.fitTot v := by
  rw [CardDemo.Cbtrn03c.fitTot, fitNum_signed rfl rfl]
  rfl

theorem lc_mod20 (L : Nat) : L % 1000000000 % 20 = L % 20 := Nat.mod_mod_of_dvd L (by decide)


/-! ### The translations' steps, field by field -/

section
variable (s : St) (l : List Nat)
@[simp] theorem dsp_disp : (dsp s l).disp = s.disp ++ [l] := rfl
@[simp] theorem dsp_writes : (dsp s l).writes = s.writes := rfl
@[simp] theorem dsp_lc : (dsp s l).lc = s.lc := rfl
@[simp] theorem dsp_page : (dsp s l).page = s.page := rfl
@[simp] theorem dsp_acct : (dsp s l).acct = s.acct := rfl
@[simp] theorem dsp_grand : (dsp s l).grand = s.grand := rfl
@[simp] theorem dsp_rs : (dsp s l).rs = s.rs := rfl
@[simp] theorem dsp_re : (dsp s l).re = s.re := rfl
@[simp] theorem dsp_first : (dsp s l).first = s.first := rfl
@[simp] theorem dsp_card : (dsp s l).card = s.card := rfl
@[simp] theorem dsp_xref : (dsp s l).xref = s.xref := rfl
@[simp] theorem wr_disp : (wr s l).disp = s.disp := rfl
@[simp] theorem wr_writes : (wr s l).writes = s.writes ++ [l] := rfl
@[simp] theorem wr_lc : (wr s l).lc = s.lc := rfl
@[simp] theorem wr_page : (wr s l).page = s.page := rfl
@[simp] theorem wr_acct : (wr s l).acct = s.acct := rfl
@[simp] theorem wr_grand : (wr s l).grand = s.grand := rfl
@[simp] theorem wr_rs : (wr s l).rs = s.rs := rfl
@[simp] theorem wr_re : (wr s l).re = s.re := rfl
@[simp] theorem wr_first : (wr s l).first = s.first := rfl
@[simp] theorem wr_card : (wr s l).card = s.card := rfl
@[simp] theorem wr_xref : (wr s l).xref = s.xref := rfl
@[simp] theorem inc_disp : (inc s).disp = s.disp := rfl
@[simp] theorem inc_writes : (inc s).writes = s.writes := rfl
@[simp] theorem inc_lc : (inc s).lc = (s.lc + 1) % 1000000000 := rfl
@[simp] theorem inc_page : (inc s).page = s.page := rfl
@[simp] theorem inc_acct : (inc s).acct = s.acct := rfl
@[simp] theorem inc_grand : (inc s).grand = s.grand := rfl
@[simp] theorem inc_rs : (inc s).rs = s.rs := rfl
@[simp] theorem inc_re : (inc s).re = s.re := rfl
@[simp] theorem inc_first : (inc s).first = s.first := rfl
@[simp] theorem inc_card : (inc s).card = s.card := rfl
@[simp] theorem inc_xref : (inc s).xref = s.xref := rfl
end

@[simp] theorem headers_eq (s : St) : headers s =
    { s with writes := s.writes ++ [nameHeader s.rs s.re, blankLine, header1, header2],
             lc := ((((s.lc + 1) % 1000000000 + 1) % 1000000000 + 1) % 1000000000 + 1) % 1000000000 } := by
  simp [headers, inc, wr]
@[simp] theorem pageTotals_eq (s : St) : pageTotals s =
    { s with writes := s.writes ++ [pageTotalLine s.page, header2],
             lc := ((s.lc + 1) % 1000000000 + 1) % 1000000000, grand := trunc11 (s.grand + s.page),
             page := 0 } := by
  simp [pageTotals, inc, wr]
@[simp] theorem acctTotals_eq (s : St) : acctTotals s =
    { s with writes := s.writes ++ [acctTotalLine s.acct, header2],
             lc := ((s.lc + 1) % 1000000000 + 1) % 1000000000, acct := 0 } := by
  simp [acctTotals, inc, wr]

/-- The fields of the translations' state after a step. -/
macro "st_proj" : tactic =>
  `(tactic| simp only [inc_card, inc_first, inc_lc, inc_page, inc_acct, inc_grand, inc_xref,
    inc_rs, inc_re, inc_disp, inc_writes, wr_card, wr_first, wr_lc, wr_page, wr_acct, wr_grand,
    wr_xref, wr_rs, wr_re, wr_disp, wr_writes, headers_eq, pageTotals_eq, acctTotals_eq,
    dsp_card, dsp_first, dsp_lc, dsp_page, dsp_acct, dsp_grand, dsp_xref, dsp_rs, dsp_re,
    dsp_disp, dsp_writes])

set_option maxHeartbeats 1000000 in
/-- One transaction in the date range whose lookups succeed: the translations' `tranStep` and
coblean's `step3` keep `Corr`. -/
theorem step_corr {xs ys cs : List (List FVal)} {d : List FVal} {S : St}
    {M : CardDemo.Cbtrn03c.M3} {T X Y C : List FVal} (hC : Corr d S M) (hT : TranRecord.Valid T)
    (hxs : ∀ x ∈ xs, CardXrefRecord.Valid x) (hys : ∀ y ∈ ys, TranTypeRecord.Valid y)
    (hcs : ∀ c ∈ cs, TranCatRecord.Valid c)
    (hX : ¬ S.card = tCard T → xs.find? (fun x => xCard x == tCard T) = some X)
    (hY : ys.find? (fun y => yType y == tType T) = some Y)
    (hCc : cs.find? (fun c => cType c == tType T && cCat c == tCat T) = some C)
    (hd : (dStart d).length = 10 ∧ (dEnd d).length = 10) :
    ∃ S', tranStep xs ys cs d S T = .ok S' ∧
      Corr d S' (CardDemo.Cbtrn03c.step3 (xs.map toXref) (ys.map TranTypeRecord.encode)
        (cs.map TranCatRecord.encode) (dStart d) (dEnd d) M (toTran T)) := by
  obtain ⟨hcard, hfirst, hlc, hpage, hacct, hgrand, hxacct, hdates, hdisp, hwr, hwl⟩ := hC
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := length_lines
  obtain ⟨-, htyl, hcatb, hcat0, -⟩ := toTran_valid hT
  have htd : CardDemo.Cbtrn03c.typeDesc (ys.map TranTypeRecord.encode) (toTran T).ty =
      (yDesc Y).take 15 := typeDesc_eq hys hY
  have hcd : CardDemo.Cbtrn03c.catDesc (cs.map TranCatRecord.encode) (toTran T).ty (toTran T).cat =
      (cDesc C).take 29 := catDesc_eq hcs htyl hcat0 hcatb hCc
  obtain ⟨yt, yd, yf, hYe, -, hyd, -⟩ := type_shape (hys Y (List.mem_of_find?_eq_some hY))
  obtain ⟨ct, cc, cdesc, cf, hCe, -, -, -, hcdl, -⟩ :=
    catg_shape (hcs C (List.mem_of_find?_eq_some hCc))
  have hYd : (yDesc Y).length = 50 := by rw [hYe]; exact hyd
  have hCd : (cDesc C).length = 50 := by rw [hCe]; exact hcdl
  have hdl := detailLine_text (X := X) hT hYd hCd
  have hnl := nameLine_text hd.1 hd.2
  have hstep : tranStep xs ys cs d S T = .ok (report d (if S.card = tCard T then
      dsp S (TranRecord.textS T) else
      { { (if S.first then dsp S (TranRecord.textS T) else acctTotals (dsp S (TranRecord.textS T)))
        with card := tCard T } with xref := X }) T Y C) := by
    unfold tranStep cardStep
    by_cases hs : S.card = tCard T
    · simp [dsp, hs, hY, hCc]
    · simp only [dsp, hs, ↓reduceIte, hX hs, hY, hCc]
      rfl
  refine ⟨_, hstep, ?_⟩
  -- the outputs of a step: the transaction's line, then the report lines
  have hdl' : ∀ X' : List FVal, cps (CardDemo.Cbtrn03c.detailLine (toTran T) (xAcct X')
      ((yDesc Y).take 15) ((cDesc C).take 29)) = detailLine T X' Y C :=
    fun X' => detailLine_text hT hYd hCd
  by_cases hs : S.card = tCard T
  · have hs' : decide (M.card = (toTran T).card) = true := by
      simp [← hcard, hs, toTran, tCard]
    simp only [hs, ↓reduceIte]
    cases hf : M.first
    · have hSf : S.first = false := by rw [hfirst, hf]
      obtain ⟨hrs, hre⟩ := hdates hSf
      by_cases hb : M.lines % 20 = 0
      · have hb' : S.lc % 20 = 0 := by rw [hlc, lc_mod20, hb]
        simp only [report, dsp, hSf, Bool.false_eq_true, ↓reduceIte, hb', ↓reduceIte]
        simp only [CardDemo.Cbtrn03c.step3, hs', hf, Bool.true_or, Bool.false_eq_true, ↓reduceIte,
          ↓reduceIte, hb, decide_true]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · st_proj; exact hs
        · st_proj
        · st_proj; rw [hlc]; clear hb' hb; simp only [Nat.mod_add_mod] <;> omega
        · st_proj; rw [trunc11_eq]; rfl
        · st_proj; rw [trunc11_eq, hacct]; rfl
        · st_proj; rw [trunc11_eq, hgrand, hpage]
        · st_proj; exact hxacct
        · st_proj; intro _; exact ⟨hrs, hre⟩
        · st_proj
          rw [hdisp, tran_cps hT]
          simp [List.reverse_cons, dispL_append, dispL_display, dispL_write, dispL_nil,
            CardDemo.Cbtrn03c.headers]
        · st_proj
          rw [hwr, htd, hcd, ← hxacct, hrs, hre, hpage]
          simp [List.reverse_cons, wrL_append, wrL_display, wrL_write, wrL_nil,
            CardDemo.Cbtrn03c.headers, pageLine_cps, hdr2_cps, hdr1_cps, blank_cps,
            nameLine_cps hd.1 hd.2, hdl']
        · st_proj
          try simp only [List.append_assoc, List.cons_append, List.nil_append]
          refine wlen_append hwl ?_
          repeat' (first | exact wlen_nil | refine wlen_cons ?_ ?_)
          all_goals first | exact length_to133 _ | simp [blankLine, header2]
      · have hb' : ¬ S.lc % 20 = 0 := by rw [hlc, lc_mod20]; exact hb
        simp only [report, dsp, hSf, Bool.false_eq_true, ↓reduceIte, hb']
        simp only [CardDemo.Cbtrn03c.step3, hs', hf, Bool.true_or, Bool.false_eq_true, ↓reduceIte,
          ↓reduceIte, hb, decide_false]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · st_proj; exact hs
        · st_proj
        · st_proj; rw [hlc]; clear hb' hb; simp only [Nat.mod_add_mod] <;> omega
        · st_proj; rw [trunc11_eq, hpage]; rfl
        · st_proj; rw [trunc11_eq, hacct]; rfl
        · st_proj; exact hgrand
        · st_proj; exact hxacct
        · st_proj; intro _; exact ⟨hrs, hre⟩
        · st_proj
          rw [hdisp, tran_cps hT]
          simp [List.reverse_cons, dispL_append, dispL_display, dispL_write, dispL_nil,
            ]
        · st_proj
          rw [hwr, htd, hcd, ← hxacct]
          simp [List.reverse_cons, wrL_append, wrL_display, wrL_write, wrL_nil, hdl']
        · st_proj
          try simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
          refine wlen_append hwl ?_
          repeat' (first | exact wlen_nil | refine wlen_cons ?_ ?_)
          all_goals first | exact length_to133 _ | simp [blankLine, header2]
    · have hSf : S.first = true := by rw [hfirst, hf]
      by_cases hb : (M.lines + 4) % 20 = 0
      · have hb' : ((((S.lc + 1) % 1000000000 + 1) % 1000000000 + 1) % 1000000000 + 1) %
            1000000000 % 20 = 0 := by rw [hlc]; omega
        simp only [report, dsp, hSf, ↓reduceIte]
        st_proj
        simp only [hb', ↓reduceIte]
        simp only [CardDemo.Cbtrn03c.step3, hs', hf, Bool.true_or, ↓reduceIte, hb,
          decide_true]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · st_proj; exact hs
        · st_proj
        · st_proj; rw [hlc]; clear hb' hb; simp only [Nat.mod_add_mod] <;> omega
        · st_proj; rw [trunc11_eq]; rfl
        · st_proj; rw [trunc11_eq, hacct]; rfl
        · st_proj; rw [trunc11_eq, hgrand, hpage]
        · st_proj; exact hxacct
        · st_proj; try simp
        · st_proj
          rw [hdisp, tran_cps hT]
          simp [List.reverse_cons, dispL_append, dispL_display, dispL_write, dispL_nil,
            CardDemo.Cbtrn03c.headers]
        · st_proj
          rw [hwr, htd, hcd, ← hxacct, hpage]
          simp [List.reverse_cons, wrL_append, wrL_display, wrL_write, wrL_nil,
            CardDemo.Cbtrn03c.headers, pageLine_cps, hdr2_cps, hdr1_cps, blank_cps,
            nameLine_cps hd.1 hd.2, hdl']
        · st_proj
          try simp only [List.append_assoc, List.cons_append, List.nil_append]
          refine wlen_append hwl ?_
          repeat' (first | exact wlen_nil | refine wlen_cons ?_ ?_)
          all_goals first | exact length_to133 _ | simp [blankLine, header2]
      · have hb' : ¬ ((((S.lc + 1) % 1000000000 + 1) % 1000000000 + 1) % 1000000000 + 1) %
            1000000000 % 20 = 0 := by rw [hlc]; omega
        simp only [report, dsp, hSf, ↓reduceIte]
        st_proj
        simp only [hb', ↓reduceIte]
        simp only [CardDemo.Cbtrn03c.step3, hs', hf, Bool.true_or, Bool.false_eq_true, ↓reduceIte, hb,
          decide_false]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · st_proj; exact hs
        · st_proj
        · st_proj; rw [hlc]; clear hb' hb; simp only [Nat.mod_add_mod] <;> omega
        · st_proj; rw [trunc11_eq, hpage]; rfl
        · st_proj; rw [trunc11_eq, hacct]; rfl
        · st_proj; exact hgrand
        · st_proj; exact hxacct
        · st_proj; try simp
        · st_proj
          rw [hdisp, tran_cps hT]
          simp [List.reverse_cons, dispL_append, dispL_display, dispL_write, dispL_nil,
            CardDemo.Cbtrn03c.headers]
        · st_proj
          rw [hwr, htd, hcd, ← hxacct]
          simp [List.reverse_cons, wrL_append, wrL_display, wrL_write, wrL_nil,
            CardDemo.Cbtrn03c.headers, hdr2_cps, hdr1_cps, blank_cps,
            nameLine_cps hd.1 hd.2, hdl']
        · st_proj
          try simp only [List.append_assoc, List.cons_append, List.nil_append]
          refine wlen_append hwl ?_
          repeat' (first | exact wlen_nil | refine wlen_cons ?_ ?_)
          all_goals first | exact length_to133 _ | simp [blankLine, header2]
  · have hs' : decide (M.card = (toTran T).card) = false := by
      rw [decide_eq_false_iff_not, ← hcard]; exact hs
    have hxa : (CardDemo.Cbtrn03c.xrefOf (xs.map toXref) (toTran T).card).acct = xAcct X := by
      rw [show (toTran T).card = tCard T from rfl, xrefOf_eq hxs (hX hs)]
      rfl
    simp only [hs, ↓reduceIte]
    cases hf : M.first
    · have hSf : S.first = false := by rw [hfirst, hf]
      obtain ⟨hrs, hre⟩ := hdates hSf
      by_cases hb : (M.lines + 2) % 20 = 0
      · have hb' : ((S.lc + 1) % 1000000000 + 1) % 1000000000 % 20 = 0 := by rw [hlc]; omega
        simp only [hSf, Bool.false_eq_true, ↓reduceIte, report, dsp, acctTotals_eq]
        st_proj
        simp only [hb', ↓reduceIte]
        simp only [CardDemo.Cbtrn03c.step3, hs', hf, Bool.false_or, Bool.false_eq_true,
          ↓reduceIte, hb, decide_true]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · st_proj; rfl
        · st_proj
        · st_proj; rw [hlc]; clear hb' hb; simp only [Nat.mod_add_mod] <;> omega
        · st_proj; rw [trunc11_eq]; rfl
        · st_proj; rw [trunc11_eq]; rfl
        · st_proj; rw [trunc11_eq, hgrand, hpage]
        · st_proj; exact hxa.symm
        · st_proj; intro _; exact ⟨hrs, hre⟩
        · st_proj
          rw [hdisp, tran_cps hT]
          simp [List.reverse_cons, dispL_append, dispL_display, dispL_write, dispL_nil,
            CardDemo.Cbtrn03c.headers]
        · st_proj
          rw [hwr, htd, hcd, hxa, hrs, hre, hpage, hacct]
          simp [List.reverse_cons, wrL_append, wrL_display, wrL_write, wrL_nil,
            CardDemo.Cbtrn03c.headers, pageLine_cps, acctLine_cps, hdr2_cps, hdr1_cps, blank_cps,
            nameLine_cps hd.1 hd.2, hdl']
        · st_proj
          try simp only [List.append_assoc, List.cons_append, List.nil_append]
          refine wlen_append hwl ?_
          repeat' (first | exact wlen_nil | refine wlen_cons ?_ ?_)
          all_goals first | exact length_to133 _ | simp [blankLine, header2]
      · have hb' : ¬ ((S.lc + 1) % 1000000000 + 1) % 1000000000 % 20 = 0 := by rw [hlc]; omega
        simp only [hSf, Bool.false_eq_true, ↓reduceIte, report, dsp, acctTotals_eq]
        st_proj
        simp only [hb', ↓reduceIte]
        simp only [CardDemo.Cbtrn03c.step3, hs', hf, Bool.false_or, Bool.false_eq_true,
          ↓reduceIte, hb, decide_false]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · st_proj; rfl
        · st_proj
        · st_proj; rw [hlc]; clear hb' hb; simp only [Nat.mod_add_mod] <;> omega
        · st_proj; rw [trunc11_eq, hpage]; rfl
        · st_proj; rw [trunc11_eq]; rfl
        · st_proj; exact hgrand
        · st_proj; exact hxa.symm
        · st_proj; intro _; exact ⟨hrs, hre⟩
        · st_proj
          rw [hdisp, tran_cps hT]
          simp [List.reverse_cons, dispL_append, dispL_display, dispL_write, dispL_nil,
            ]
        · st_proj
          rw [hwr, htd, hcd, hxa, hacct]
          simp [List.reverse_cons, wrL_append, wrL_display, wrL_write, wrL_nil,
            acctLine_cps, hdr2_cps,
             hdl']
        · st_proj
          try simp only [List.append_assoc, List.cons_append, List.nil_append]
          refine wlen_append hwl ?_
          repeat' (first | exact wlen_nil | refine wlen_cons ?_ ?_)
          all_goals first | exact length_to133 _ | simp [header2]
    · have hSf : S.first = true := by rw [hfirst, hf]
      by_cases hb : (M.lines + 4) % 20 = 0
      · have hb' : ((((S.lc + 1) % 1000000000 + 1) % 1000000000 + 1) % 1000000000 + 1) %
            1000000000 % 20 = 0 := by rw [hlc]; omega
        simp only [hSf, ↓reduceIte, report, dsp]
        st_proj
        simp only [hb', ↓reduceIte]
        simp only [CardDemo.Cbtrn03c.step3, hs', hf, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hb,
          decide_true]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · st_proj; rfl
        · st_proj
        · st_proj; rw [hlc]; clear hb' hb; simp only [Nat.mod_add_mod] <;> omega
        · st_proj; rw [trunc11_eq]; rfl
        · st_proj; rw [trunc11_eq, hacct]; rfl
        · st_proj; rw [trunc11_eq, hgrand, hpage]
        · st_proj; exact hxa.symm
        · st_proj; try simp
        · st_proj
          rw [hdisp, tran_cps hT]
          simp [List.reverse_cons, dispL_append, dispL_display, dispL_write, dispL_nil,
            CardDemo.Cbtrn03c.headers]
        · st_proj
          rw [hwr, htd, hcd, hxa, hpage]
          simp [List.reverse_cons, wrL_append, wrL_display, wrL_write, wrL_nil,
            CardDemo.Cbtrn03c.headers, pageLine_cps, hdr2_cps, hdr1_cps, blank_cps,
            nameLine_cps hd.1 hd.2, hdl']
        · st_proj
          try simp only [List.append_assoc, List.cons_append, List.nil_append]
          refine wlen_append hwl ?_
          repeat' (first | exact wlen_nil | refine wlen_cons ?_ ?_)
          all_goals first | exact length_to133 _ | simp [blankLine, header2]
      · have hb' : ¬ ((((S.lc + 1) % 1000000000 + 1) % 1000000000 + 1) % 1000000000 + 1) %
            1000000000 % 20 = 0 := by rw [hlc]; omega
        simp only [hSf, ↓reduceIte, report, dsp]
        st_proj
        simp only [hb', ↓reduceIte]
        simp only [CardDemo.Cbtrn03c.step3, hs', hf, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hb,
          decide_false]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · st_proj; rfl
        · st_proj
        · st_proj; rw [hlc]; clear hb' hb; simp only [Nat.mod_add_mod] <;> omega
        · st_proj; rw [trunc11_eq, hpage]; rfl
        · st_proj; rw [trunc11_eq, hacct]; rfl
        · st_proj; exact hgrand
        · st_proj; exact hxa.symm
        · st_proj; try simp
        · st_proj
          rw [hdisp, tran_cps hT]
          simp [List.reverse_cons, dispL_append, dispL_display, dispL_write, dispL_nil,
            CardDemo.Cbtrn03c.headers]
        · st_proj
          rw [hwr, htd, hcd, hxa]
          simp [List.reverse_cons, wrL_append, wrL_display, wrL_write, wrL_nil,
            CardDemo.Cbtrn03c.headers, hdr2_cps, hdr1_cps, blank_cps,
            nameLine_cps hd.1 hd.2, hdl']
        · st_proj
          try simp only [List.append_assoc, List.cons_append, List.nil_append]
          refine wlen_append hwl ?_
          repeat' (first | exact wlen_nil | refine wlen_cons ?_ ?_)
          all_goals first | exact length_to133 _ | simp [blankLine, header2]

/-! ## The date test -/

theorem cmpB_eq : ∀ a b : List UInt8, cmpB a b = Sem.cmpBytes a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by simp only [cmpB, Sem.cmpBytes, cmpB_eq xs ys]

/-- The date parameter record as the program reads it: the record padded to the file's 80
bytes. -/
def parmOf (d : List FVal) : List UInt8 := WsDateparmRecord.encode d ++ List.replicate 59 64

theorem parm_shape {d : List FVal} (hd : WsDateparmRecord.Valid d) :
    ∃ st f en, d = [.str st, .str f, .str en] ∧ st.length = 10 ∧ f.length = 1 ∧
      en.length = 10 := by
  have hl : d.length = 3 := hd.length_eq.symm
  match d, hl, hd with
  | [x0, x1, x2], _, .cons h0 (.cons h1 (.cons h2 .nil)) =>
    obtain ⟨st, rfl, hst⟩ := str_of_valid rfl h0
    obtain ⟨f, rfl, hf⟩ := str_of_valid rfl h1
    obtain ⟨en, rfl, hen⟩ := str_of_valid rfl h2
    exact ⟨st, f, en, rfl, hst, hf, hen⟩

theorem parm_dates {d : List FVal} (hd : WsDateparmRecord.Valid d) :
    (parmOf d).take 10 = dStart d ∧ ((parmOf d).drop 11).take 10 = dEnd d ∧
      (parmOf d).length = 80 ∧ (dStart d).length = 10 ∧ (dEnd d).length = 10 := by
  obtain ⟨st, f, en, rfl, hst, hf, hen⟩ := parm_shape hd
  have e : parmOf [.str st, .str f, .str en] = st ++ (f ++ (en ++ List.replicate 59 64)) := by
    show (st ++ (f ++ (en ++ []))) ++ List.replicate 59 64 = _
    simp [List.append_assoc]
  rw [e]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.take_left' hst]; rfl
  · rw [← List.append_assoc, List.drop_left' (by simp [hst, hf]), List.take_left' hen]; rfl
  · simp [hst, hf, hen]
  · exact hst
  · exact hen

/-- The date test of the translations is coblean's. -/
theorem inRange_iff {d t : List FVal} (hd : WsDateparmRecord.Valid d) :
    CardDemo.Cbtrn03c.inRange (parmOf d) (toTran t) ↔ inRange d t = true := by
  obtain ⟨h1, h2, -⟩ := parm_dates hd
  simp only [CardDemo.Cbtrn03c.inRange, Model.inRange, h1, h2, cmpB_eq, Bool.and_eq_true,
    bne_iff_ne, ne_eq]
  rfl

/-! ## The keyed lookups that fail -/

theorem findKey_isNone {α : Type} [Inhabited α] {k : KeyDecl} {v : List UInt8}
    {g : α → List UInt8} {p : α → Bool} {l : List α}
    (hp : ∀ x ∈ l, (Sem.keyOf k (g x) == v) = p x) :
    (Sem.findKey k v (l.map g)).isNone = (l.find? p).isNone := by
  rw [← findKey_map k v g p l hp]
  cases Sem.findKey k v (l.map g) <;> rfl

theorem xref_hp {xs : List (List FVal)} (hxs : ∀ x ∈ xs, CardXrefRecord.Valid x)
    (card : List UInt8) : ∀ x ∈ xs.map toXref,
      (Sem.keyOf { off := 0, len := 16 } x.bytes == card) = (x.card == card) := by
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx
  obtain ⟨c, cu, a, f, rfl, hc, -⟩ := xref_shape (hxs x0 hx0)
  simp only [Sem.keyOf, List.drop_zero, Xref.bytes, toXref, xCard, strOf, List.append_assoc,
    List.getD_cons_zero]
  rw [List.take_left' hc]

theorem xref_none {xs : List (List FVal)} (hxs : ∀ x ∈ xs, CardXrefRecord.Valid x)
    (card : List UInt8) :
    (Sem.findKey { off := 0, len := 16 } card ((xs.map toXref).map Xref.bytes)).isNone =
      (xs.find? (fun x => xCard x == card)).isNone := by
  rw [findKey_isNone (xref_hp hxs card), List.find?_map]
  show (Option.map toXref (xs.find? (fun x => xCard x == card))).isNone = _
  cases xs.find? (fun x => xCard x == card) <;> rfl

theorem type_hp {ys : List (List FVal)} (hys : ∀ y ∈ ys, TranTypeRecord.Valid y)
    (ty : List UInt8) : ∀ y ∈ ys,
      (Sem.keyOf { off := 0, len := 2 } (TranTypeRecord.encode y) == ty) = (yType y == ty) := by
  intro y hy
  obtain ⟨t, d, f, rfl, ht, -⟩ := type_shape (hys y hy)
  show (Sem.keyOf { off := 0, len := 2 } (t ++ (d ++ (f ++ []))) == ty) = _
  simp only [Sem.keyOf, List.drop_zero, List.take_left' ht, yType, strOf, List.getD_cons_zero]

theorem type_none {ys : List (List FVal)} (hys : ∀ y ∈ ys, TranTypeRecord.Valid y)
    (ty : List UInt8) :
    (Sem.findKey { off := 0, len := 2 } ty (ys.map TranTypeRecord.encode)).isNone =
      (ys.find? (fun y => yType y == ty)).isNone := findKey_isNone (type_hp hys ty)

theorem cat_hp {cs : List (List FVal)} (hcs : ∀ c ∈ cs, TranCatRecord.Valid c)
    {ty : List UInt8} {cat : Int} (hty : ty.length = 2) (hcat0 : 0 ≤ cat)
    (hcat : cat.natAbs < 10000) : ∀ c ∈ cs,
      (Sem.keyOf { off := 0, len := 6 } (TranCatRecord.encode c) ==
        ty ++ encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt cat) =
        (cType c == ty && cCat c == cat) := by
  have henc : ∀ c, (encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt c).length = 4 := fun c =>
    (length_encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt c (by decide)).trans rfl
  intro c hc
  obtain ⟨t, k, d, f, rfl, ht, hk, hk0, -⟩ := catg_shape (hcs c hc)
  show (Sem.keyOf { off := 0, len := 6 }
    (t ++ (encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt k ++ (d ++ (f ++ [])))) == _) = _
  have hkey : Sem.keyOf { off := 0, len := 6 }
      (t ++ (encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt k ++ (d ++ (f ++ [])))) =
      t ++ encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt k := by
    simp only [Sem.keyOf, List.drop_zero]
    rw [← List.append_assoc]
    exact List.take_left' (by simp [ht, henc])
  rw [hkey]
  simp only [cType, cCat, strOf, numOf, List.getD_cons_zero, List.getD_cons_succ]
  have hb := encodeNum_beq (f := CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt) (by decide) (by decide)
    ((holds_display rfl).2 ⟨hk, fun _ => hk0⟩) ((holds_display rfl).2 ⟨hcat, fun _ => hcat0⟩)
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, Bool.and_eq_true]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [ht, hty])
    refine ⟨h1, ?_⟩
    have := hb
    rw [h2, beq_self_eq_true] at this
    exact (beq_iff_eq.1 this.symm)
  · rintro ⟨rfl, rfl⟩; rfl

theorem cat_none {cs : List (List FVal)} (hcs : ∀ c ∈ cs, TranCatRecord.Valid c)
    {ty : List UInt8} {cat : Int} (hty : ty.length = 2) (hcat0 : 0 ≤ cat)
    (hcat : cat.natAbs < 10000) :
    (Sem.findKey { off := 0, len := 6 } (ty ++ encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt cat)
      (cs.map TranCatRecord.encode)).isNone =
      (cs.find? (fun c => cType c == ty && cCat c == cat)).isNone :=
  findKey_isNone (cat_hp hcs hty hcat0 hcat)

/-! ## The messages -/

theorem startMsg_cps : cps CardDemo.Cbtrn03c.startMsg =
    txt "START OF EXECUTION OF PROGRAM CBTRN03C" := by decide +kernel
theorem endMsg_cps : cps CardDemo.Cbtrn03c.endMsg =
    txt "END OF EXECUTION OF PROGRAM CBTRN03C" := by decide +kernel
theorem reportingMsg_cps : cps CardDemo.Cbtrn03c.reportingMsg = txt "Reporting from " := by
  decide +kernel
theorem toMsg_cps : cps CardDemo.Cbtrn03c.toMsg = txt " to " := by decide +kernel
theorem amtMsg_cps : cps CardDemo.Cbtrn03c.amtMsg = txt "TRAN-AMT " := by decide +kernel
theorem pageMsg_cps : cps CardDemo.Cbtrn03c.pageMsg = txt "WS-PAGE-TOTAL" := by decide +kernel
theorem invCardMsg_cps : cps CardDemo.Cbtrn03c.invCardMsg = txt "INVALID CARD NUMBER : " := by
  decide +kernel
theorem invTypeMsg_cps :
    cps CardDemo.Cbtrn03c.invTypeMsg = txt "INVALID TRANSACTION TYPE : " := by decide +kernel
theorem invCatMsg_cps : cps CardDemo.Cbtrn03c.invCatMsg = txt "INVALID TRAN CATG KEY : " := by
  decide +kernel
theorem status_cps : cps (CardDemo.Cbtrn03c.statusMsg ++ [240, 240, 242, 243]) =
    txt "FILE STATUS IS: NNNN0023" := by decide +kernel
theorem abendMsg_cps : cps CardDemo.Cbtrn03c.abendMsg = txt "ABENDING PROGRAM" := by
  decide +kernel

theorem amt_cps (v : Int) : cps (encodeNum {} CardDemo.Cbtrn03c.TRAN_AMT.fmt v) = zoned 11 v :=
  text_signed rfl rfl rfl rfl v
theorem pageTot_cps (v : Int) :
    cps (encodeNum {} CardDemo.Cbtrn03c.WS_PAGE_TOTAL.fmt v) = zoned 11 v :=
  text_signed rfl rfl rfl rfl v
theorem catCd_cps (v : Int) :
    cps (encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt v) = digs 4 v :=
  text_unsigned rfl rfl (by decide) v

/-! ## A failed lookup: the abend -/

/-- The outputs of the translations' state `S` are those of coblean's events `M.out`. -/
structure OutCorr (d : List FVal) (S : St) (M : CardDemo.Cbtrn03c.M3) : Prop where
  disp : S.disp = txt "START OF EXECUTION OF PROGRAM CBTRN03C" ::
    (txt "Reporting from " ++ cps (dStart d) ++ txt " to " ++ cps (dEnd d)) ::
    (dispL M.out.reverse).map cps
  writes : S.writes = (wrL 5 M.out.reverse).map cps
  wlen : ∀ l ∈ S.writes, l.length = 133

theorem Corr.out {d : List FVal} {S : St} {M : CardDemo.Cbtrn03c.M3} (h : Corr d S M) :
    OutCorr d S M := ⟨h.disp, h.writes, h.wlen⟩

@[simp] theorem abend23_disp (s : St) (msg : List Nat) : (abend23 s msg).disp =
    s.disp ++ [msg, txt "FILE STATUS IS: NNNN0023", txt "ABENDING PROGRAM"] := by
  simp [abend23, dsp]
@[simp] theorem abend23_writes (s : St) (msg : List Nat) : (abend23 s msg).writes = s.writes := rfl

/-- The abend after the displays and writes of a transaction (`same || first`: no account
total). -/
theorem abend_corr {d : List FVal} {S : St} {M : CardDemo.Cbtrn03c.M3} {T : List FVal}
    (hC : Corr d S M) (hT : TranRecord.Valid T) (s2 : St) (msg : List UInt8)
    (hsame : (decide (M.card = (toTran T).card) || M.first) = true)
    (hd2 : s2.disp = S.disp ++ [TranRecord.textS T]) (hw2 : s2.writes = S.writes) :
    OutCorr d (abend23 s2 (cps msg))
      { M with out := CardDemo.Cbtrn03c.abendEvents msg ++
        (if (decide (M.card = (toTran T).card) || M.first) = true then
          Event.display (toTran T).bytes :: M.out
        else Event.write 5 CardDemo.Cbtrn03c.hdr2Line ::
          Event.write 5 (CardDemo.Cbtrn03c.acctLine M.acct) :: Event.display (toTran T).bytes :: M.out) } := by
  obtain ⟨-, -, -, -, -, -, -, -, hdisp, hwr, hwl⟩ := hC
  simp only [hsame, ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩
  · rw [abend23_disp, hd2, hdisp, tran_cps hT]
    simp [CardDemo.Cbtrn03c.abendEvents, List.reverse_cons, dispL_append, dispL_display,
      dispL_nil, status_cps, abendMsg_cps]
  · rw [abend23_writes, hw2, hwr]
    simp [CardDemo.Cbtrn03c.abendEvents, List.reverse_cons, wrL_append, wrL_display, wrL_nil]
  · rw [abend23_writes, hw2]; exact hwl

/-- The abend after a change of card, the account total written. -/
theorem abend_corr' {d : List FVal} {S : St} {M : CardDemo.Cbtrn03c.M3} {T : List FVal}
    (hC : Corr d S M) (hT : TranRecord.Valid T) (s2 : St) (msg : List UInt8)
    (hsame : (decide (M.card = (toTran T).card) || M.first) = false)
    (hd2 : s2.disp = S.disp ++ [TranRecord.textS T])
    (hw2 : s2.writes = S.writes ++ [acctTotalLine S.acct, header2]) :
    OutCorr d (abend23 s2 (cps msg))
      { M with out := CardDemo.Cbtrn03c.abendEvents msg ++
        (if (decide (M.card = (toTran T).card) || M.first) = true then
          Event.display (toTran T).bytes :: M.out
        else Event.write 5 CardDemo.Cbtrn03c.hdr2Line ::
          Event.write 5 (CardDemo.Cbtrn03c.acctLine M.acct) :: Event.display (toTran T).bytes :: M.out) } := by
  obtain ⟨-, -, -, -, hacct, -, -, -, hdisp, hwr, hwl⟩ := hC
  obtain ⟨-, -, l3, -, -, l6, -, -⟩ := length_lines
  simp only [hsame, Bool.false_eq_true, ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩
  · rw [abend23_disp, hd2, hdisp, tran_cps hT]
    simp [CardDemo.Cbtrn03c.abendEvents, List.reverse_cons, dispL_append, dispL_display,
      dispL_write, dispL_nil, status_cps, abendMsg_cps]
  · rw [abend23_writes, hw2, hwr, hacct]
    simp [CardDemo.Cbtrn03c.abendEvents, List.reverse_cons, wrL_append, wrL_display, wrL_write,
      wrL_nil, acctLine_cps, hdr2_cps]
  · rw [abend23_writes, hw2]
    exact wlen_append hwl (wlen_cons (l6 _) (wlen_cons l3 wlen_nil))

/-! ## The loop over the transaction file -/

/-- What the translations' loop gives for what coblean's model says of the transactions: a report
still going (the loop goes on to the end of the file, with `tl` in the record area), stopped by
a date out of range (the loop ends), or abended by a failed lookup. -/
def LoopCorr (xs ys cs : List (List FVal)) (d tl : List FVal) (r : Except St St) :
    CardDemo.Cbtrn03c.X3 → Prop
  | .go M => ∃ S, Corr d S M ∧ r = loop xs ys cs d [] tl S
  | .stop M => ∃ S, Corr d S M ∧ r = .ok S
  | .abend M => ∃ S, OutCorr d S M ∧ r = .error S

theorem isSome_of_find {α : Type} {o : Option α} {a : α} (h : o = some a) : o.isNone = false := by
  rw [h]; rfl

theorem isSome_of_isNone {α : Type} {o : Option α} (h : o.isNone = false) : o.isSome = true := by
  cases o <;> simp_all

set_option maxHeartbeats 1000000 in
/-- **The loop**: the translations' loop and coblean's `report3x`, transaction by transaction. -/
theorem loop_corr {xs ys cs : List (List FVal)} {d : List FVal}
    (hxs : ∀ x ∈ xs, CardXrefRecord.Valid x) (hys : ∀ y ∈ ys, TranTypeRecord.Valid y)
    (hcs : ∀ c ∈ cs, TranCatRecord.Valid c) (hdv : WsDateparmRecord.Valid d) :
    ∀ (ts : List (List FVal)) (tran : List FVal) (S : St) (M : CardDemo.Cbtrn03c.M3), Corr d S M →
      (∀ t ∈ ts, TranRecord.Valid t) →
      LoopCorr xs ys cs d ((tran :: ts).getLast (List.cons_ne_nil _ _)) (loop xs ys cs d ts tran S)
        ((ts.map toTran).foldl (CardDemo.Cbtrn03c.step3x (xs.map toXref)
          (ys.map TranTypeRecord.encode) (cs.map TranCatRecord.encode) (parmOf d)) (.go M))
  | [], tran, S, M, hC, _ => ⟨S, hC, rfl⟩
  | t :: ts, tran, S, M, hC, hts => by
    have hT := hts t (by simp)
    have hts' : ∀ t' ∈ ts, TranRecord.Valid t' := fun t' h' => hts t' (by simp [h'])
    have hlast : (tran :: t :: ts).getLast (List.cons_ne_nil _ _) =
        (t :: ts).getLast (List.cons_ne_nil _ _) := List.getLast_cons _
    obtain ⟨-, htyl, hcatb, hcat0, -⟩ := toTran_valid hT
    have hdd := parm_dates hdv
    simp only [List.map_cons, List.foldl_cons]
    by_cases hin : inRange d t = true
    · have hinC : CardDemo.Cbtrn03c.inRange (parmOf d) (toTran t) := (inRange_iff hdv).2 hin
      have hloop : ∀ s1, tranStep xs ys cs d S t = .error s1 →
          loop xs ys cs d (t :: ts) tran S = .error s1 := by
        intro s1 hr; simp only [loop, hin, ↓reduceIte, hr]
      have hloopok : ∀ s1, tranStep xs ys cs d S t = .ok s1 →
          loop xs ys cs d (t :: ts) tran S = loop xs ys cs d ts t s1 := by
        intro s1 hr; simp only [loop, hin, ↓reduceIte, hr]
      have hcard := hC.card
      by_cases hs : S.card = tCard t
      · have hs' : decide (M.card = (toTran t).card) = true := by simp [← hcard, hs, toTran, tCard]
        cases hY : ys.find? (fun y => yType y == tType t) with
        | none =>
          -- the type lookup fails
          have htn : (Sem.findKey { off := 0, len := 2 } (toTran t).ty
              (ys.map TranTypeRecord.encode)).isNone = true := by
            rw [type_none hys]; rw [show (toTran t).ty = tType t from rfl, hY]; rfl
          have hstep : CardDemo.Cbtrn03c.step3x (xs.map toXref) (ys.map TranTypeRecord.encode)
              (cs.map TranCatRecord.encode) (parmOf d) (.go M) (toTran t) =
              .abend { M with out := CardDemo.Cbtrn03c.abendEvents (CardDemo.Cbtrn03c.invTypeMsg ++
                (toTran t).ty) ++ (if (decide (M.card = (toTran t).card) || M.first) = true then
                  Event.display (toTran t).bytes :: M.out
                else Event.write 5 CardDemo.Cbtrn03c.hdr2Line ::
                  Event.write 5 (CardDemo.Cbtrn03c.acctLine M.acct) ::
                    Event.display (toTran t).bytes :: M.out) } := by
            simp only [CardDemo.Cbtrn03c.step3x, hinC, ↓reduceIte, hs', Bool.not_true,
              Bool.false_and, Bool.false_eq_true, htn]
          rw [hstep, CardDemo.Cbtrn03c.foldl_step3x_abend]
          refine ⟨_, abend_corr hC hT (dsp S (TranRecord.textS t)) _ (by simp [hs']) rfl rfl, ?_⟩
          have htr : tranStep xs ys cs d S t = .error (abend23 (dsp S (TranRecord.textS t))
              (txt "INVALID TRANSACTION TYPE : " ++ cps (tType t))) := by
            unfold tranStep cardStep; simp [dsp, hs, hY]
          rw [hloop _ htr, cps_append, invTypeMsg_cps]
          rfl
        | some Y =>
          cases hCc : cs.find? (fun c => cType c == tType t && cCat c == tCat t) with
          | none =>
            have hcn : (Sem.findKey { off := 0, len := 6 } ((toTran t).ty ++
                encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt (toTran t).cat)
                (cs.map TranCatRecord.encode)).isNone = true := by
              rw [cat_none hcs htyl hcat0 hcatb]
              rw [show (toTran t).ty = tType t from rfl, show (toTran t).cat = tCat t from rfl, hCc]
              rfl
            have hstep : CardDemo.Cbtrn03c.step3x (xs.map toXref) (ys.map TranTypeRecord.encode)
                (cs.map TranCatRecord.encode) (parmOf d) (.go M) (toTran t) =
                .abend { M with out := CardDemo.Cbtrn03c.abendEvents (CardDemo.Cbtrn03c.invCatMsg ++
                  (toTran t).ty ++ encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt (toTran t).cat) ++
                  (if (decide (M.card = (toTran t).card) || M.first) = true then
                    Event.display (toTran t).bytes :: M.out
                  else Event.write 5 CardDemo.Cbtrn03c.hdr2Line ::
                    Event.write 5 (CardDemo.Cbtrn03c.acctLine M.acct) ::
                      Event.display (toTran t).bytes :: M.out) } := by
              have htn : (Sem.findKey { off := 0, len := 2 } (toTran t).ty
                  (ys.map TranTypeRecord.encode)).isNone = false := by
                rw [type_none hys]; exact isSome_of_find hY
              simp only [CardDemo.Cbtrn03c.step3x, hinC, ↓reduceIte, hs', Bool.not_true,
                Bool.false_and, Bool.false_eq_true, htn, hcn]
            rw [hstep, CardDemo.Cbtrn03c.foldl_step3x_abend]
            refine ⟨_, abend_corr hC hT (dsp S (TranRecord.textS t)) _ (by simp [hs']) rfl rfl, ?_⟩
            have htr : tranStep xs ys cs d S t = .error (abend23 (dsp S (TranRecord.textS t))
                (txt "INVALID TRAN CATG KEY : " ++ cps (tType t) ++ digs 4 (tCat t))) := by
              unfold tranStep cardStep; simp [dsp, hs, hY, hCc]
            rw [hloop _ htr, cps_append, cps_append, invCatMsg_cps, catCd_cps]
            rfl
          | some C =>
            obtain ⟨S1, hS1, hC1⟩ := step_corr (X := []) hC hT hxs hys hcs (fun h => absurd hs h)
              hY hCc ⟨hdd.2.2.2.1, hdd.2.2.2.2⟩
            have hstep : CardDemo.Cbtrn03c.step3x (xs.map toXref) (ys.map TranTypeRecord.encode)
                (cs.map TranCatRecord.encode) (parmOf d) (.go M) (toTran t) =
                .go (CardDemo.Cbtrn03c.step3 (xs.map toXref) (ys.map TranTypeRecord.encode)
                  (cs.map TranCatRecord.encode) (dStart d) (dEnd d) M (toTran t)) := by
              rw [CardDemo.Cbtrn03c.step3x_go _ _ _ _ _ _ hinC (fun h => absurd (hcard ▸ hs) h)
                (isSome_of_isNone (by rw [type_none hys]; exact isSome_of_find hY))
                (isSome_of_isNone (by rw [cat_none hcs htyl hcat0 hcatb]; exact isSome_of_find hCc)),
                hdd.1, hdd.2.1]
            rw [hstep]
            have ih := loop_corr hxs hys hcs hdv ts t S1 _ hC1 hts'
            rw [hloopok _ hS1, hlast]
            exact ih
      · have hs' : decide (M.card = (toTran t).card) = false := by
          rw [decide_eq_false_iff_not, ← hcard]; exact hs
        -- the state after the account total (if any) and the card change
        have hpre : ∀ X : List FVal,
            ({ { (if S.first = true then dsp S (TranRecord.textS t)
                else acctTotals (dsp S (TranRecord.textS t))) with card := tCard t } with xref := X }
              : St).disp = S.disp ++ [TranRecord.textS t] ∧
            (M.first = true → ({ { (if S.first = true then dsp S (TranRecord.textS t)
                else acctTotals (dsp S (TranRecord.textS t))) with card := tCard t } with xref := X }
              : St).writes = S.writes) ∧
            (M.first = false → ({ { (if S.first = true then dsp S (TranRecord.textS t)
                else acctTotals (dsp S (TranRecord.textS t))) with card := tCard t } with xref := X }
              : St).writes = S.writes ++ [acctTotalLine S.acct, header2]) := by
          intro X
          refine ⟨?_, fun hf => ?_, fun hf => ?_⟩
          · cases S.first <;> simp [dsp]
          · simp [hC.first, hf, dsp]
          · simp [hC.first, hf, dsp]
        cases hX : xs.find? (fun x => xCard x == tCard t) with
        | none =>
          have hxn : (Sem.findKey { off := 0, len := 16 } (toTran t).card
              ((xs.map toXref).map Xref.bytes)).isNone = true := by
            rw [xref_none hxs]; rw [show (toTran t).card = tCard t from rfl, hX]; rfl
          have hstep : CardDemo.Cbtrn03c.step3x (xs.map toXref) (ys.map TranTypeRecord.encode)
              (cs.map TranCatRecord.encode) (parmOf d) (.go M) (toTran t) =
              .abend { M with out := CardDemo.Cbtrn03c.abendEvents (CardDemo.Cbtrn03c.invCardMsg ++
                (toTran t).card) ++ (if (decide (M.card = (toTran t).card) || M.first) = true then
                  Event.display (toTran t).bytes :: M.out
                else Event.write 5 CardDemo.Cbtrn03c.hdr2Line ::
                  Event.write 5 (CardDemo.Cbtrn03c.acctLine M.acct) ::
                    Event.display (toTran t).bytes :: M.out) } := by
            simp only [CardDemo.Cbtrn03c.step3x, hinC, ↓reduceIte, hs', Bool.not_false,
              Bool.true_and, hxn]
          rw [hstep, CardDemo.Cbtrn03c.foldl_step3x_abend]
          have htr : tranStep xs ys cs d S t = .error (abend23
              { (if S.first = true then dsp S (TranRecord.textS t)
                else acctTotals (dsp S (TranRecord.textS t))) with card := tCard t }
              (txt "INVALID CARD NUMBER : " ++ cps (tCard t))) := by
            unfold tranStep cardStep; simp [dsp, hs, hX]
          obtain ⟨hd1, hw1, hw1'⟩ := hpre []
          rcases Bool.eq_false_or_eq_true M.first with hf | hf
          · refine ⟨_, abend_corr hC hT { (if S.first = true then dsp S (TranRecord.textS t)
                else acctTotals (dsp S (TranRecord.textS t))) with card := tCard t } _
                (by simp [hs', hf]) hd1 (hw1 hf), ?_⟩
            rw [hloop _ htr, cps_append, invCardMsg_cps]
            rfl
          · refine ⟨_, abend_corr' hC hT { (if S.first = true then dsp S (TranRecord.textS t)
                else acctTotals (dsp S (TranRecord.textS t))) with card := tCard t } _
                (by simp [hs', hf]) hd1 (hw1' hf), ?_⟩
            rw [hloop _ htr, cps_append, invCardMsg_cps]
            rfl
        | some X =>
          have hxs' : (Sem.findKey { off := 0, len := 16 } (toTran t).card
              ((xs.map toXref).map Xref.bytes)).isNone = false := by
            rw [xref_none hxs]; exact isSome_of_find hX
          obtain ⟨hd1, hw1, hw1'⟩ := hpre X
          cases hY : ys.find? (fun y => yType y == tType t) with
          | none =>
            have htn : (Sem.findKey { off := 0, len := 2 } (toTran t).ty
                (ys.map TranTypeRecord.encode)).isNone = true := by
              rw [type_none hys]; rw [show (toTran t).ty = tType t from rfl, hY]; rfl
            have hstep : CardDemo.Cbtrn03c.step3x (xs.map toXref) (ys.map TranTypeRecord.encode)
                (cs.map TranCatRecord.encode) (parmOf d) (.go M) (toTran t) =
                .abend { M with out := CardDemo.Cbtrn03c.abendEvents (CardDemo.Cbtrn03c.invTypeMsg ++
                  (toTran t).ty) ++ (if (decide (M.card = (toTran t).card) || M.first) = true then
                    Event.display (toTran t).bytes :: M.out
                  else Event.write 5 CardDemo.Cbtrn03c.hdr2Line ::
                    Event.write 5 (CardDemo.Cbtrn03c.acctLine M.acct) ::
                      Event.display (toTran t).bytes :: M.out) } := by
              simp only [CardDemo.Cbtrn03c.step3x, hinC, ↓reduceIte, hs', Bool.not_false,
                Bool.true_and, hxs', Bool.false_eq_true, htn]
            rw [hstep, CardDemo.Cbtrn03c.foldl_step3x_abend]
            have htr : tranStep xs ys cs d S t = .error (abend23
                { { (if S.first = true then dsp S (TranRecord.textS t)
                  else acctTotals (dsp S (TranRecord.textS t))) with card := tCard t } with xref := X }
                (txt "INVALID TRANSACTION TYPE : " ++ cps (tType t))) := by
              unfold tranStep cardStep; simp [dsp, hs, hX, hY]
            rcases Bool.eq_false_or_eq_true M.first with hf | hf
            · refine ⟨_, abend_corr hC hT _ _ (by simp [hs', hf]) hd1 (hw1 hf), ?_⟩
              rw [hloop _ htr, cps_append, invTypeMsg_cps]
              rfl
            · refine ⟨_, abend_corr' hC hT _ _ (by simp [hs', hf]) hd1 (hw1' hf), ?_⟩
              rw [hloop _ htr, cps_append, invTypeMsg_cps]
              rfl
          | some Y =>
            have htn : (Sem.findKey { off := 0, len := 2 } (toTran t).ty
                (ys.map TranTypeRecord.encode)).isNone = false := by
              rw [type_none hys]; exact isSome_of_find hY
            cases hCc : cs.find? (fun c => cType c == tType t && cCat c == tCat t) with
            | none =>
              have hcn : (Sem.findKey { off := 0, len := 6 } ((toTran t).ty ++
                  encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt (toTran t).cat)
                  (cs.map TranCatRecord.encode)).isNone = true := by
                rw [cat_none hcs htyl hcat0 hcatb]
                rw [show (toTran t).ty = tType t from rfl, show (toTran t).cat = tCat t from rfl,
                  hCc]
                rfl
              have hstep : CardDemo.Cbtrn03c.step3x (xs.map toXref) (ys.map TranTypeRecord.encode)
                  (cs.map TranCatRecord.encode) (parmOf d) (.go M) (toTran t) =
                  .abend { M with out := CardDemo.Cbtrn03c.abendEvents (CardDemo.Cbtrn03c.invCatMsg ++
                    (toTran t).ty ++ encodeNum {} CardDemo.Cbtrn03c.FD_TRAN_CAT_CD.fmt (toTran t).cat) ++
                    (if (decide (M.card = (toTran t).card) || M.first) = true then
                      Event.display (toTran t).bytes :: M.out
                    else Event.write 5 CardDemo.Cbtrn03c.hdr2Line ::
                      Event.write 5 (CardDemo.Cbtrn03c.acctLine M.acct) ::
                        Event.display (toTran t).bytes :: M.out) } := by
                simp only [CardDemo.Cbtrn03c.step3x, hinC, ↓reduceIte, hs', Bool.not_false,
                  Bool.true_and, hxs', Bool.false_eq_true, htn, hcn]
              rw [hstep, CardDemo.Cbtrn03c.foldl_step3x_abend]
              have htr : tranStep xs ys cs d S t = .error (abend23
                  { { (if S.first = true then dsp S (TranRecord.textS t)
                    else acctTotals (dsp S (TranRecord.textS t))) with card := tCard t } with xref := X }
                  (txt "INVALID TRAN CATG KEY : " ++ cps (tType t) ++ digs 4 (tCat t))) := by
                unfold tranStep cardStep; simp [dsp, hs, hX, hY, hCc]
              rcases Bool.eq_false_or_eq_true M.first with hf | hf
              · refine ⟨_, abend_corr hC hT _ _ (by simp [hs', hf]) hd1 (hw1 hf), ?_⟩
                rw [hloop _ htr, cps_append, cps_append, invCatMsg_cps, catCd_cps]
                rfl
              · refine ⟨_, abend_corr' hC hT _ _ (by simp [hs', hf]) hd1 (hw1' hf), ?_⟩
                rw [hloop _ htr, cps_append, cps_append, invCatMsg_cps, catCd_cps]
                rfl
            | some C =>
              obtain ⟨S1, hS1, hC1⟩ := step_corr hC hT hxs hys hcs (fun _ => hX) hY hCc
                ⟨hdd.2.2.2.1, hdd.2.2.2.2⟩
              have hstep : CardDemo.Cbtrn03c.step3x (xs.map toXref) (ys.map TranTypeRecord.encode)
                  (cs.map TranCatRecord.encode) (parmOf d) (.go M) (toTran t) =
                  .go (CardDemo.Cbtrn03c.step3 (xs.map toXref) (ys.map TranTypeRecord.encode)
                    (cs.map TranCatRecord.encode) (dStart d) (dEnd d) M (toTran t)) := by
                rw [CardDemo.Cbtrn03c.step3x_go _ _ _ _ _ _ hinC
                  (fun _ => isSome_of_isNone hxs') (isSome_of_isNone htn)
                  (isSome_of_isNone (by rw [cat_none hcs htyl hcat0 hcatb]; exact isSome_of_find hCc)),
                  hdd.1, hdd.2.1]
              rw [hstep]
              have ih := loop_corr hxs hys hcs hdv ts t S1 _ hC1 hts'
              rw [hloopok _ hS1, hlast]
              exact ih
    · have hinC : ¬ CardDemo.Cbtrn03c.inRange (parmOf d) (toTran t) :=
        fun h => hin ((inRange_iff hdv).1 h)
      have hstep : CardDemo.Cbtrn03c.step3x (xs.map toXref) (ys.map TranTypeRecord.encode)
          (cs.map TranCatRecord.encode) (parmOf d) (.go M) (toTran t) = .stop M := by
        simp [CardDemo.Cbtrn03c.step3x, hinC]
      rw [hstep, CardDemo.Cbtrn03c.foldl_step3x_stop]
      exact ⟨S, hC, by simp [loop, hin]⟩

/-! ## The end of the file, the start -/

/-- The end of the file with the record `tl` in the record area: its amount and the page total
displayed, the amount added once more, the page and grand totals written. -/
theorem eof_corr {d : List FVal} {S : St} {M : CardDemo.Cbtrn03c.M3} (tl : List FVal)
    (hC : Corr d S M) :
    OutCorr d (eofTail S tl) { M with out := CardDemo.Cbtrn03c.eofEvents M (toTran tl) ++ M.out } := by
  obtain ⟨-, -, -, hpage, -, hgrand, -, -, hdisp, hwr, hwl⟩ := hC
  obtain ⟨-, -, l3, -, l5, -, l7, -⟩ := length_lines
  refine ⟨?_, ?_, ?_⟩
  · simp only [eofTail, grandTotals, pageTotals_eq, wr_disp, dsp_disp]
    rw [hdisp]
    simp [CardDemo.Cbtrn03c.eofEvents, List.reverse_cons, dispL_append, dispL_display,
      dispL_write, dispL_nil, amtMsg_cps, pageMsg_cps, amt_cps, cps_append, hpage,
      toTran, tAmt]
  · simp only [eofTail, grandTotals, pageTotals_eq, wr_writes, dsp_writes, dsp_page, dsp_grand]
    rw [hwr]
    simp [CardDemo.Cbtrn03c.eofEvents, List.reverse_cons, wrL_append, wrL_display, wrL_write,
      wrL_nil, pageLine_cps, grandLine_cps, hdr2_cps, trunc11_eq, hpage, hgrand, toTran, tAmt]
  · simp only [eofTail, grandTotals, pageTotals_eq, wr_writes, dsp_writes]
    exact wlen_append (wlen_append hwl (wlen_cons (l5 _) (wlen_cons l3 wlen_nil)))
      (wlen_cons (l7 _) wlen_nil)

/-- The state after the date range is displayed, before the first transaction. -/
theorem init_corr (d : List FVal) :
    Corr d (dsp init (txt "Reporting from " ++ cps (dStart d) ++ txt " to " ++ cps (dEnd d)))
      (CardDemo.Cbtrn03c.init3 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => by simp [dsp, init] at h, rfl, rfl,
    fun _ h => by simp [dsp, init] at h⟩

/-! ## The COBOL run -/

cobol_mem_hex initMem from "init_mem.hex"

set_option maxRecDepth 10000 in
theorem initMem_size : initMem.size = 2309 := by rfl

set_option maxRecDepth 100000 in
/-- The record area of the harness storage holds `tran0` (spaces and zeros). -/
theorem initMem_tran0 : initMem.read 733 350 = (toTran tran0).bytes := by decide +kernel

set_option maxRecDepth 100000 in
/-- The account id of `CARD-XREF-RECORD` in the harness storage: zero. -/
theorem initMem_xacct : initMem.read 1110 11 = encodeNum {} CardDemo.Cbtrn03c.XREF_ACCT_ID.fmt 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tran0_valid : (toTran tran0).valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## The outputs of the run -/

set_option maxRecDepth 100000 in
theorem ebc_cp037 : ∀ n, n < 256 → ebc (cp037Code (UInt8.ofNat n)) = UInt8.ofNat n := by
  decide +kernel

theorem ebc_cps (b : List UInt8) : (cps b).map ebc = b := by
  simp only [cps, List.map_map]
  conv => rhs; rw [← List.map_id b]
  apply List.map_congr_left
  intro x _
  have h := ebc_cp037 x.toNat (UInt8.toNat_lt x)
  simp only [UInt8.ofNat_toNat] at h
  simp only [Function.comp_apply, id_eq]
  exact h

theorem rept_decode {b : List UInt8} (hb : b.length = 133) :
    FdReptfileRec.decode b = some [.str b] := by
  simp [Schema.decode, Field.decode, Field.bytes, List.take_of_length_le, hb]

theorem getLast_map_getD {α β : Type} (f : α → β) (a : α) (l : List α) :
    (l.map f).getLast?.getD (f a) = f ((a :: l).getLast (List.cons_ne_nil _ _)) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    rw [List.getLast_cons (List.cons_ne_nil _ _), ← ih b]
    simp [List.getLast?_cons]

theorem map_cps : (fun x : List UInt8 => x.map cp037Code) = cps := rfl

/-- The displays and the written records of a run whose events are `ev ++ M.out ++ header3`
(`ev`: the end message, unless the run abended). -/
theorem final_outputs {d : List FVal} {S : St} {M : CardDemo.Cbtrn03c.M3}
    (hO : OutCorr d S M) (hdv : WsDateparmRecord.Valid d) (ab : Bool) :
    ((dispL ((if ab then [] else [Event.display CardDemo.Cbtrn03c.endMsg]) ++ M.out ++
        CardDemo.Cbtrn03c.header3 (parmOf d)).reverse).map cps = (out S ab).disp) ∧
      ((wrL 5 ((if ab then [] else [Event.display CardDemo.Cbtrn03c.endMsg]) ++ M.out ++
        CardDemo.Cbtrn03c.header3 (parmOf d)).reverse).map FdReptfileRec.decode =
        (out S ab).writes.map some) := by
  obtain ⟨hdisp, hwr, hwl⟩ := hO
  obtain ⟨h1, h2, -⟩ := parm_dates hdv
  have hh : (CardDemo.Cbtrn03c.header3 (parmOf d)).reverse =
      [Event.display CardDemo.Cbtrn03c.startMsg, Event.display (CardDemo.Cbtrn03c.reportingMsg ++
        (parmOf d).take 10 ++ CardDemo.Cbtrn03c.toMsg ++ ((parmOf d).drop 11).take 10)] := rfl
  refine ⟨?_, ?_⟩
  · rw [List.reverse_append, List.reverse_append, hh]
    cases ab <;> simp [out, hdisp, dispL_append, dispL_display, dispL_nil, cps_append,
      startMsg_cps, reportingMsg_cps, toMsg_cps, endMsg_cps, h1, h2]
  · rw [List.reverse_append, List.reverse_append, hh]
    have hw : (wrL 5 M.out.reverse).map FdReptfileRec.decode =
        (S.writes.map fun l => [FVal.str (l.map ebc)]).map some := by
      rw [hwr, List.map_map, List.map_map]
      apply List.map_congr_left
      intro b hb
      have hl : (cps b).length = 133 := hwl _ (by rw [hwr]; exact List.mem_map_of_mem hb)
      rw [length_cps] at hl
      simp [rept_decode hl, ebc_cps]
    cases ab <;> simp [out, wrL_append, wrL_display, wrL_nil, hw]

/-- **CBTRN03C's COBOL run outputs what `Model.run` says**, for every input of the statements'
domain (`Domain`: fewer than 10^7 transactions and a date parameter record; dates out of range end
the report early and failed lookups abend, in both): the run ends with GOBACK or abends with code
999, as `Model.run`'s `abended` says; its displays (code points) and the report lines it writes
(decoded) are `Model.run`'s. -/
theorem cobol_outputs (vals1 vals2 vals3 vals4 vals5 : List (List FVal))
    (hv1 : ∀ v ∈ vals1, TranRecord.Valid v) (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, TranTypeRecord.Valid v) (hv4 : ∀ v ∈ vals4, TranCatRecord.Valid v)
    (hv5 : ∀ v ∈ vals5, WsDateparmRecord.Valid v) (hD : Domain vals1 vals2 vals3 vals4 vals5)
    (n : Nat) (hn : vals1.length < n) :
    let r := CardDemo.Cbtrn03c.run {} (n + 60) (CardDemo.Cbtrn03c.initState initMem
      [(1, vals1.map TranRecord.encode), (2, vals2.map CardXrefRecord.encode),
        (3, vals3.map TranTypeRecord.encode), (4, vals4.map TranCatRecord.encode),
        (6, vals5.map (fun r => WsDateparmRecord.encode r ++ List.replicate 59 64))])
    let o := Model.run vals1 vals2 vals3 vals4 vals5
    (r.1 = .stop .goback ∨ r.1 = .fault (.abend 999)) ∧
      (displays r.2).map (·.map cp037Code) = o.disp ∧
      (writes 5 r.2).map FdReptfileRec.decode = o.writes.map some ∧
      abended r.1 = o.abended := by
  dsimp only
  obtain ⟨hlen, hpne⟩ := hD
  obtain ⟨d, rest, rfl⟩ : ∃ d rest, vals5 = d :: rest := by
    cases vals5 with
    | nil => exact absurd rfl hpne
    | cons d rest => exact ⟨d, rest, rfl⟩
  have hdv := hv5 d (by simp)
  have hdd := parm_dates hdv
  have hf1 : vals1.map TranRecord.encode = (vals1.map toTran).map Tran.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun t ht => (toTran_bytes (hv1 t ht)).symm)
  have hf2 : vals2.map CardXrefRecord.encode = (vals2.map toXref).map Xref.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun x hx => (toXref_bytes (hv2 x hx)).symm)
  have hf6 : (d :: rest).map (fun r => WsDateparmRecord.encode r ++ List.replicate 59 64) =
      parmOf d :: rest.map parmOf := rfl
  have hx := CardDemo.Cbtrn03c.cbtrn03c_every initMem initMem_size (vals1.map toTran)
    (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht; exact toTran_valid (hv1 t0 ht0))
    (by rw [List.length_map]; exact hlen) (toTran tran0)
    (fun _ => ⟨tran0_valid, initMem_tran0⟩) 0 (fun _ => ⟨initMem_xacct, by decide, by decide⟩)
    (vals2.map toXref)
    (by intro x hx; obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx; exact toXref_valid (hv2 x0 hx0))
    (vals3.map TranTypeRecord.encode) (vals4.map TranCatRecord.encode)
    (by intro r hr; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr
        exact Schema.length_encode (by decide) (hv3 y hy))
    (by intro r hr; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
        exact Schema.length_encode (by decide) (hv4 c hc))
    (parmOf d) hdd.2.2.1 (rest.map parmOf) n (by rw [List.length_map]; exact hn)
  rw [hf6]
  simp only [← hf1, ← hf2] at hx
  obtain ⟨hsig, hout⟩ := hx
  rw [hsig, displays_eq, writes_eq, hout, getLast_map_getD toTran tran0 vals1, map_cps]
  have hL := loop_corr (xs := vals2) (ys := vals3) (cs := vals4) hv2 hv3 hv4 hdv vals1 tran0 _ _
    (init_corr d) hv1
  simp only [Model.run]
  generalize (tran0 :: vals1).getLast (List.cons_ne_nil _ _) = tl at hL ⊢
  generalize loop vals2 vals3 vals4 d vals1 tran0
    (dsp init (txt "Reporting from " ++ cps (dStart d) ++ txt " to " ++ cps (dEnd d))) = res at hL ⊢
  unfold CardDemo.Cbtrn03c.report3xe
  generalize (vals1.map toTran).foldl (CardDemo.Cbtrn03c.step3x (vals2.map toXref)
    (vals3.map TranTypeRecord.encode) (vals4.map TranCatRecord.encode) (parmOf d))
    (.go (CardDemo.Cbtrn03c.init3 0)) = x at hL ⊢
  cases x with
  | go M =>
    obtain ⟨S, hC, rfl⟩ := hL
    simp only [CardDemo.Cbtrn03c.result3, loop]
    by_cases hin : inRange d tl = true
    · have hinC : CardDemo.Cbtrn03c.inRange (parmOf d) (toTran tl) := (inRange_iff hdv).2 hin
      simp only [hin, hinC, ↓reduceIte]
      obtain ⟨h1, h2⟩ := final_outputs (eof_corr tl hC) hdv false
      refine ⟨by simp, ?_, ?_, rfl⟩
      · rw [← h1]; simp [List.append_assoc]
      · rw [← h2]; simp [List.append_assoc]
    · have hinC : ¬ CardDemo.Cbtrn03c.inRange (parmOf d) (toTran tl) :=
        fun h => hin ((inRange_iff hdv).1 h)
      simp only [hin, hinC, ↓reduceIte, Bool.false_eq_true]
      obtain ⟨h1, h2⟩ := final_outputs hC.out hdv false
      refine ⟨by simp, ?_, ?_, rfl⟩
      · rw [← h1]; simp [List.append_assoc]
      · rw [← h2]; simp [List.append_assoc]
  | stop M =>
    obtain ⟨S, hC, rfl⟩ := hL
    simp only [CardDemo.Cbtrn03c.result3]
    obtain ⟨h1, h2⟩ := final_outputs hC.out hdv false
    refine ⟨by simp, ?_, ?_, rfl⟩
    · rw [← h1]; simp [List.append_assoc]
    · rw [← h2]; simp [List.append_assoc]
  | abend M =>
    obtain ⟨S, hO, rfl⟩ := hL
    simp only [CardDemo.Cbtrn03c.result3]
    obtain ⟨h1, h2⟩ := final_outputs hO hdv true
    refine ⟨by simp, ?_, ?_, rfl⟩
    · rw [← h1]; simp
    · rw [← h2]; simp

end EquivLean.Modernize.Cbtrn03c.Glue
