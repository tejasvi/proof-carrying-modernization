import EquivLean.Bridge.Cobol.Records
import EquivLean.Demo.Cobol.Cbtrn01c.Prog

/-!
# CBTRN01C: the lines the translations display, from the input field values

CBTRN01C reads the daily transactions; for each it DISPLAYs the record, then looks up its card
in the cross-reference file and the card's account in the account file, DISPLAYing what it finds;
after the end of file it does the lookups once more for the last record read (the record area's
initial contents when the file is empty), then DISPLAYs the end message (coblean's
`cbtrn01c_verifies_all`).

`displayText`: these lines as code points, a function of the field values of the transaction,
cross-reference and account records, computed as the translations do (a numeric field's digits,
an alphanumeric field's text, the string literals).  The Java contract maps the lines to UTF-16
strings; the Rust contract uses them as they are.  `displayText_eq`: for valid field values they are
the CP037 texts of the lines in coblean's theorem.
-/

open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn01c.Model

cobol_schema DalytranRecord from "../../../examples/cobol/carddemo/cbtrn01c.ir.json" record "DALYTRAN-RECORD"
theorem dalytranRecord_contig : DalytranRecord.Contig := by decide
cobol_schema CardXrefRecord from "../../../examples/cobol/carddemo/cbtrn01c.ir.json" record "CARD-XREF-RECORD"
theorem cardXrefRecord_contig : CardXrefRecord.Contig := by decide
cobol_schema AccountRecord from "../../../examples/cobol/carddemo/cbtrn01c.ir.json" record "ACCOUNT-RECORD"
theorem accountRecord_contig : AccountRecord.Contig := by decide
cobol_mem_hex initMem from "init_mem.hex"

/-- The bytes of an alphanumeric value. -/
def strOf : FVal → List UInt8
  | .str bs => bs
  | .num _ => []

/-- The integer of a numeric value. -/
def numOf : FVal → Int
  | .num v => v
  | .str _ => 0

/-- The code points of a string literal. -/
def txt (s : String) : List Nat := s.toList.map Char.toNat

/-- What the lookups display for the transaction `t`: 2000-LOOKUP-XREF (the first
cross-reference record with the card number of `t`), then, if it is found, 3000-READ-ACCOUNT (the
first account record with the cross-reference's account id). -/
def lookupText (xrefs accts : List (List FVal)) (t : List FVal) : List (List Nat) :=
  match xrefs.find? (fun x => strOf (x.getD 0 default) == strOf (t.getD 10 default)) with
  | none =>
    [txt "INVALID CARD NUMBER FOR XREF",
      txt "CARD NUMBER " ++ (strOf (t.getD 10 default)).map cp037Code ++
        txt " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-" ++
        (strOf (t.getD 0 default)).map cp037Code]
  | some x =>
    [txt "SUCCESSFUL READ OF XREF", txt "CARD NUMBER: " ++ (strOf (x.getD 0 default)).map cp037Code,
      txt "ACCOUNT ID : " ++ zpad 11 (numOf (x.getD 2 default)).natAbs,
      txt "CUSTOMER ID: " ++ zpad 9 (numOf (x.getD 1 default)).natAbs] ++
    match accts.find? (fun a => numOf (a.getD 0 default) == numOf (x.getD 2 default)) with
    | none => [txt "INVALID ACCOUNT NUMBER FOUND",
        txt "ACCOUNT " ++ zpad 11 (numOf (x.getD 2 default)).natAbs ++ txt " NOT FOUND"]
    | some _ => [txt "SUCCESSFUL READ OF ACCOUNT FILE"]

/-- The initial values of `DALYTRAN-RECORD` (the harness storage: spaces and zeros). -/
def dal0 : List FVal :=
  [.str (List.replicate 16 64), .str (List.replicate 2 64), .num 0, .str (List.replicate 10 64),
    .str (List.replicate 100 64), .num 0, .num 0, .str (List.replicate 50 64),
    .str (List.replicate 50 64), .str (List.replicate 10 64), .str (List.replicate 16 64),
    .str (List.replicate 26 64), .str (List.replicate 26 64), .str (List.replicate 20 64)]

/-- The lines CBTRN01C displays, as code points. -/
def displayText (trans xrefs accts : List (List FVal)) : List (List Nat) :=
  txt "START OF EXECUTION OF PROGRAM CBTRN01C" ::
    (trans.flatMap (fun t => DalytranRecord.textS t :: lookupText xrefs accts t) ++
      lookupText xrefs accts (trans.getLast?.getD dal0) ++
      [txt "END OF EXECUTION OF PROGRAM CBTRN01C"])

/-! ## The lines are the CP037 texts of coblean's -/

/-- The cross-reference record of coblean's model with the field values `x`. -/
def xrefOf (x : List FVal) : CardDemo.Cbtrn01c.Xref :=
  ⟨strOf (x.getD 0 default), numOf (x.getD 1 default), numOf (x.getD 2 default),
    strOf (x.getD 3 default)⟩

theorem cardXref_fields : CardXrefRecord.fields.length = 4 := rfl

theorem xrefOf_bytes {x : List FVal} (hx : CardXrefRecord.Valid x) :
    (xrefOf x).bytes = CardXrefRecord.encode x ∧ (xrefOf x).valid := by
  have hl : x.length = 4 := hx.length_eq.symm
  match x, hl, hx with
  | [x0, x1, x2, x3], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))) =>
    cases x0 with
    | num _ => obtain ⟨fmt, hk, -⟩ := h0; cases hk
    | str c =>
    cases x3 with
    | num _ => obtain ⟨fmt, hk, -⟩ := h3; cases hk
    | str f =>
    cases x1 with
    | str _ => obtain ⟨⟨j, hk⟩, -⟩ := h1; cases hk
    | num cu =>
    cases x2 with
    | str _ => obtain ⟨⟨j, hk⟩, -⟩ := h2; cases hk
    | num ac =>
    obtain ⟨-, hc⟩ := h0
    obtain ⟨-, hf⟩ := h3
    obtain ⟨fmt1, hk1, -, -, hh1, -⟩ := h1
    obtain ⟨fmt2, hk2, -, -, hh2, -⟩ := h2
    cases hk1; cases hk2
    simp only [NumFmt.Holds, NumFmt.fullBinary] at hh1 hh2
    have e : CardXrefRecord.encode [.str c, .num cu, .num ac, .str f] =
        c ++ (encodeNum {} CardDemo.Cbtrn01c.XREF_CUST_ID.fmt cu ++
          (encodeNum {} CardDemo.Cbtrn01c.XREF_ACCT_ID.fmt ac ++ (f ++ []))) := rfl
    refine ⟨?_, hc, ?_, ?_, ?_, ?_, hf⟩
    · rw [e]
      simp [xrefOf, strOf, numOf, CardDemo.Cbtrn01c.Xref.bytes, List.append_assoc]
    all_goals simp_all [xrefOf, numOf]

theorem startMsg_text : CardDemo.Cbtrn01c.startMsg.map cp037Code =
    txt "START OF EXECUTION OF PROGRAM CBTRN01C" := by decide +kernel
theorem endMsg_text : CardDemo.Cbtrn01c.endMsg.map cp037Code =
    txt "END OF EXECUTION OF PROGRAM CBTRN01C" := by decide +kernel
theorem okXrefMsg_text : CardDemo.Cbtrn01c.okXrefMsg.map cp037Code =
    txt "SUCCESSFUL READ OF XREF" := by decide +kernel
theorem cardNumMsg_text : CardDemo.Cbtrn01c.cardNumMsg.map cp037Code =
    txt "CARD NUMBER: " := by decide +kernel
theorem acctIdMsg_text : CardDemo.Cbtrn01c.acctIdMsg.map cp037Code =
    txt "ACCOUNT ID : " := by decide +kernel
theorem custIdMsg_text : CardDemo.Cbtrn01c.custIdMsg.map cp037Code =
    txt "CUSTOMER ID: " := by decide +kernel
theorem okAcctMsg_text : CardDemo.Cbtrn01c.okAcctMsg.map cp037Code =
    txt "SUCCESSFUL READ OF ACCOUNT FILE" := by decide +kernel
theorem invCardMsg_text : CardDemo.Cbtrn01c.invCardMsg.map cp037Code =
    txt "INVALID CARD NUMBER FOR XREF" := by decide +kernel
theorem cardMsg_text : CardDemo.Cbtrn01c.cardMsg.map cp037Code =
    txt "CARD NUMBER " := by decide +kernel
theorem skipMsg_text : CardDemo.Cbtrn01c.skipMsg.map cp037Code =
    txt " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-" := by decide +kernel
theorem invAcctMsg_text : CardDemo.Cbtrn01c.invAcctMsg.map cp037Code =
    txt "INVALID ACCOUNT NUMBER FOUND" := by decide +kernel
theorem acctMsg_text : CardDemo.Cbtrn01c.acctMsg.map cp037Code =
    txt "ACCOUNT " := by decide +kernel
theorem notFoundMsg_text : CardDemo.Cbtrn01c.notFoundMsg.map cp037Code =
    txt " NOT FOUND" := by decide +kernel

/-- The account key of an account record: its `ACCT-ID` bytes. -/
theorem acct_key {a : List FVal} (ha : AccountRecord.Valid a) :
    Sem.keyOf { off := 0, len := 11 } (AccountRecord.encode a) =
      encodeNum {} CardDemo.Cbtrn01c.FD_ACCT_ID.fmt (numOf (a.getD 0 default)) ∧
    CardDemo.Cbtrn01c.FD_ACCT_ID.fmt.Holds {} (numOf (a.getD 0 default)) := by
  have hb := Schema.bytes_encode_getD accountRecord_contig ha 0 (by decide)
  have hv := Forall2.getD ha 0 (by decide)
  have hk : (AccountRecord.fields.getD 0 default).desc.kind =
      .num CardDemo.Cbtrn01c.FD_ACCT_ID.fmt := rfl
  have hl : (AccountRecord.fields.getD 0 default).desc.len = 11 := rfl
  have hr : (AccountRecord.fields.getD 0 default).roff = 0 := rfl
  have hkey : Sem.keyOf { off := 0, len := 11 } (AccountRecord.encode a) =
      (AccountRecord.fields.getD 0 default).bytes (AccountRecord.encode a) := by
    simp only [Sem.keyOf, Field.bytes, hr, hl]
  rw [hkey, hb]
  cases h0 : a.getD 0 default with
  | str bs => rw [h0] at hv; obtain ⟨⟨j, hj⟩, -⟩ := hv; rw [hk] at hj; cases hj
  | num v =>
    rw [h0] at hv
    obtain ⟨fmt, hk', -, -, hh, -⟩ := hv
    rw [hk] at hk'
    cases hk'
    exact ⟨by simp only [Field.encode, hk, numOf], hh⟩

/-- **What the lookups display, as coblean's lines.** -/
theorem lookupText_eq {xs accs : List (List FVal)} (hxs : ∀ x ∈ xs, CardXrefRecord.Valid x)
    (haccs : ∀ a ∈ accs, AccountRecord.Valid a) (t : List FVal) (T : List UInt8)
    (hcard : (T.drop 262).take 16 = strOf (t.getD 10 default))
    (hid : T.take 16 = strOf (t.getD 0 default)) :
    lookupText xs accs t =
      (CardDemo.Cbtrn01c.lookupMsgs (xs.map xrefOf) (accs.map AccountRecord.encode) T).map
        (·.map cp037Code) := by
  have hk : ∀ x ∈ xs, (Sem.keyOf { off := 0, len := 16 } ((CardDemo.Cbtrn01c.Xref.bytes ∘ xrefOf) x) ==
      (T.drop 262).take 16) = (strOf (x.getD 0 default) == strOf (t.getD 10 default)) := by
    intro x hx
    obtain ⟨-, hv⟩ := xrefOf_bytes (hxs x hx)
    have hc : (xrefOf x).card.length = 16 := hv.1
    simp only [Function.comp_apply, Sem.keyOf, CardDemo.Cbtrn01c.Xref.bytes, List.drop_zero, hcard,
      List.append_assoc]
    rw [List.take_left' hc]
    rfl
  have hf := findKey_map { off := 0, len := 16 } ((T.drop 262).take 16)
    (CardDemo.Cbtrn01c.Xref.bytes ∘ xrefOf) _ xs hk
  unfold CardDemo.Cbtrn01c.lookupMsgs lookupText
  simp only [List.map_map]
  cases h : Sem.findKey { off := 0, len := 16 } ((T.drop 262).take 16)
      (List.map (CardDemo.Cbtrn01c.Xref.bytes ∘ xrefOf) xs) with
  | none =>
    rw [h] at hf
    simp only [Option.map_none] at hf
    rw [← hf]
    simp only [List.map_cons, List.map_nil, List.map_append, invCardMsg_text, cardMsg_text,
      skipMsg_text, hcard, ← hid]
  | some i =>
    rw [h] at hf
    have hi : i < xs.length := by simpa using findKey_lt' h
    simp only [Option.map_some] at hf
    rw [← hf]
    have hx : (xs.map xrefOf).getD i default = xrefOf (xs.getD i default) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hxv := hxs _ (CardDemo.Cbtrn01c.getD_mem hi)
    dsimp only
    rw [hx]
    obtain ⟨-, hxv'⟩ := xrefOf_bytes hxv
    have hacct : CardDemo.Cbtrn01c.FD_ACCT_ID.fmt.Holds {} (xrefOf (xs.getD i default)).acct := by
      unfold NumFmt.Holds
      simp only [NumFmt.fullBinary]
      exact ⟨hxv'.2.2.2.1, fun _ => hxv'.2.2.2.2.1⟩
    have hka : ∀ a ∈ accs, (Sem.keyOf { off := 0, len := 11 } (AccountRecord.encode a) ==
        encodeNum {} CardDemo.Cbtrn01c.FD_ACCT_ID.fmt (xrefOf (xs.getD i default)).acct) =
        (numOf (a.getD 0 default) == numOf ((xs.getD i default).getD 2 default)) := by
      intro a ha
      obtain ⟨e, hh⟩ := acct_key (haccs a ha)
      rw [e]
      exact encodeNum_beq (by decide) (by decide) hh hacct
    have hfa := findKey_map { off := 0, len := 11 }
      (encodeNum {} CardDemo.Cbtrn01c.FD_ACCT_ID.fmt (xrefOf (xs.getD i default)).acct)
      AccountRecord.encode _ accs hka
    have tA : (encodeNum {} CardDemo.Cbtrn01c.XREF_ACCT_ID.fmt
        (xrefOf (xs.getD i default)).acct).map cp037Code =
        zpad 11 (numOf ((xs.getD i default).getD 2 default)).natAbs :=
      text_unsigned rfl rfl (by decide) _
    have tC : (encodeNum {} CardDemo.Cbtrn01c.XREF_CUST_ID.fmt
        (xrefOf (xs.getD i default)).cust).map cp037Code =
        zpad 9 (numOf ((xs.getD i default).getD 1 default)).natAbs :=
      text_unsigned rfl rfl (by decide) _
    cases ha : Sem.findKey { off := 0, len := 11 }
        (encodeNum {} CardDemo.Cbtrn01c.FD_ACCT_ID.fmt (xrefOf (xs.getD i default)).acct)
        (List.map AccountRecord.encode accs) with
    | none =>
      rw [ha] at hfa
      simp only [Option.map_none] at hfa
      rw [← hfa]
      simp only [List.map_cons, List.map_nil, List.map_append, okXrefMsg_text, cardNumMsg_text,
        acctIdMsg_text, custIdMsg_text, invAcctMsg_text, acctMsg_text, notFoundMsg_text, tA, tC,
        List.cons_append, List.nil_append, List.append_assoc]
      rfl
    | some j =>
      rw [ha] at hfa
      simp only [Option.map_some] at hfa
      rw [← hfa]
      simp only [List.map_cons, List.map_nil, List.map_append, okXrefMsg_text, cardNumMsg_text,
        acctIdMsg_text, custIdMsg_text, okAcctMsg_text, tA, tC, List.cons_append, List.nil_append]
      rfl

theorem dalytran_display : ∀ f ∈ DalytranRecord.fields, DisplayNumeric f := by decide

/-- The card number and the transaction id of a transaction record. -/
theorem tran_fields {t : List FVal} (ht : DalytranRecord.Valid t) :
    ((DalytranRecord.encode t).drop 262).take 16 = strOf (t.getD 10 default) ∧
    (DalytranRecord.encode t).take 16 = strOf (t.getD 0 default) := by
  have h10 := Schema.bytes_encode_getD dalytranRecord_contig ht 10 (by decide)
  have h0 := Schema.bytes_encode_getD dalytranRecord_contig ht 0 (by decide)
  have v10 := Forall2.getD ht 10 (by decide)
  have v0 := Forall2.getD ht 0 (by decide)
  have k10 : (DalytranRecord.fields.getD 10 default).desc.kind = .alnum false := rfl
  have k0 : (DalytranRecord.fields.getD 0 default).desc.kind = .alnum false := rfl
  have r10 : (DalytranRecord.fields.getD 10 default).roff = 262 := rfl
  have l10 : (DalytranRecord.fields.getD 10 default).desc.len = 16 := rfl
  have r0 : (DalytranRecord.fields.getD 0 default).roff = 0 := rfl
  have l0 : (DalytranRecord.fields.getD 0 default).desc.len = 16 := rfl
  constructor
  · cases e : t.getD 10 default with
    | num v => rw [e] at v10; obtain ⟨fmt, hk, -⟩ := v10; rw [k10] at hk; cases hk
    | str bs => rw [e] at h10; simpa [Field.bytes, Field.encode, r10, l10, strOf] using h10
  · cases e : t.getD 0 default with
    | num v => rw [e] at v0; obtain ⟨fmt, hk, -⟩ := v0; rw [k0] at hk; cases hk
    | str bs => rw [e] at h0; simpa [Field.bytes, Field.encode, r0, l0, strOf] using h0

theorem init_card : ((initMem.read 1700 350).drop 262).take 16 = strOf (dal0.getD 10 default) := by
  decide +kernel

theorem init_id : (initMem.read 1700 350).take 16 = strOf (dal0.getD 0 default) := by
  decide +kernel

/-- **The lines CBTRN01C displays are the CP037 texts of coblean's**, for valid field values. -/
theorem displayText_eq {trans xs accs : List (List FVal)} (ht : ∀ t ∈ trans, DalytranRecord.Valid t)
    (hxs : ∀ x ∈ xs, CardXrefRecord.Valid x) (haccs : ∀ a ∈ accs, AccountRecord.Valid a) :
    displayText trans xs accs =
      ([CardDemo.Cbtrn01c.startMsg] ++
        (trans.map DalytranRecord.encode).flatMap (fun t => t ::
          CardDemo.Cbtrn01c.lookupMsgs (xs.map xrefOf) (accs.map AccountRecord.encode) t) ++
        CardDemo.Cbtrn01c.lookupMsgs (xs.map xrefOf) (accs.map AccountRecord.encode)
          ((trans.map DalytranRecord.encode).getLast?.getD (initMem.read 1700 350)) ++
        [CardDemo.Cbtrn01c.endMsg]).map (·.map cp037Code) := by
  have hlast : lookupText xs accs (trans.getLast?.getD dal0) =
      (CardDemo.Cbtrn01c.lookupMsgs (xs.map xrefOf) (accs.map AccountRecord.encode)
        ((trans.map DalytranRecord.encode).getLast?.getD (initMem.read 1700 350))).map
          (·.map cp037Code) := by
    rw [List.getLast?_map]
    cases e : trans.getLast? with
    | none => exact lookupText_eq hxs haccs dal0 _ init_card init_id
    | some t =>
      have htv := ht t (List.mem_of_getLast? e)
      exact lookupText_eq hxs haccs t _ (tran_fields htv).1 (tran_fields htv).2
  have hbody : trans.flatMap (fun t => DalytranRecord.textS t :: lookupText xs accs t) =
      ((trans.map DalytranRecord.encode).flatMap (fun t => t ::
          CardDemo.Cbtrn01c.lookupMsgs (xs.map xrefOf) (accs.map AccountRecord.encode) t)).map
        (·.map cp037Code) := by
    rw [List.flatMap_map, List.map_flatMap]
    apply flatMap_congr_mem
    intro t htm
    have htv := ht t htm
    rw [List.map_cons, Schema.textS_eq dalytran_display htv,
      lookupText_eq hxs haccs t _ (tran_fields htv).1 (tran_fields htv).2]
  simp only [displayText, List.map_append, List.map_cons, List.map_nil, startMsg_text,
    endMsg_text, List.cons_append, List.nil_append, hbody, hlast]

end EquivLean.Modernize.Cbtrn01c.Model
