import EquivLean.Bridge.Cobol.Records

/-!
# Record schemas from coblean's IR (test)

`cobol_schema` on two CardDemo records: CBACT02C's `CARD-RECORD` (150 bytes) and CBACT04C's
`ACCOUNT-RECORD` (300 bytes).  The field names follow the translations' naming rule, the offsets
are those of coblean's layout (the same as the hand-written decoder of
`Demo/Jimple/Cbact04c/Decode.lean`: balance at 12, cycle credit at 78, cycle debit at 90, group id
at 112), the fields tile the record (`decide`), and decoding the record built from valid field
values gives them back.
-/

namespace EquivLean.Test.CobolRecords

open EquivLean.Cobol.Rec

cobol_schema CardRecord from "../../examples/cobol/carddemo/cbact02c.ir.json" record "CARD-RECORD"
cobol_schema AccountRecord from "../../examples/cobol/carddemo/cbact04c.ir.json" record "ACCOUNT-RECORD"

theorem cardRecord_contig : CardRecord.Contig := by decide
theorem accountRecord_contig : AccountRecord.Contig := by decide

example : CardRecord.len = 150 ∧ AccountRecord.len = 300 := ⟨rfl, rfl⟩

example : CardRecord.fields.map (fun f => (f.jname, f.rname, f.roff)) =
    [("cardNum", "card_num", 0), ("cardAcctId", "card_acct_id", 16), ("cardCvvCd", "card_cvv_cd", 27),
     ("cardEmbossedName", "card_embossed_name", 30),
     ("cardExpiraionDate", "card_expiraion_date", 80), ("cardActiveStatus", "card_active_status", 90),
     ("filler1", "filler1", 91)] := by decide

example : (AccountRecord.fields.map (fun f => (f.jname, f.roff))).filter
    (fun p => p.1 ∈ ["acctCurrBal", "acctCurrCycCredit", "acctCurrCycDebit", "acctGroupId"]) =
    [("acctCurrBal", 12), ("acctCurrCycCredit", 78), ("acctCurrCycDebit", 90), ("acctGroupId", 112)] := by
  decide

theorem cardRecord_decode_encode (vals : List FVal) (hv : CardRecord.Valid vals) :
    CardRecord.decode (CardRecord.encode vals) = some vals :=
  Schema.decode_encode cardRecord_contig hv

theorem cardRecord_length_encode (vals : List FVal) (hv : CardRecord.Valid vals) :
    (CardRecord.encode vals).length = 150 :=
  Schema.length_encode cardRecord_contig hv

end EquivLean.Test.CobolRecords
