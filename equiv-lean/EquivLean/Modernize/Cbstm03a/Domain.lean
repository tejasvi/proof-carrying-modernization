import EquivLean.Bridge.Cobol.Records
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Model

/-!
# CBSTM03A: Domain of `stm_run_sorted`, `stm_run_abort_cust`, and `stm_run_abort_acct`

The transaction file is nonempty, sorted by card number (`CardsSorted`), and has at most 50
same-card groups (`grp`) of at most 10 transactions each.
-/

open Cobol Cobol.StmCore EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbstm03a

namespace StmBridge

cobol_schema TrnxRecord from "../../../examples/cobol/carddemo/cbstm03ab.ir.json" record "TRNX-RECORD"
cobol_schema CardXrefRecord from "../../../examples/cobol/carddemo/cbstm03ab.ir.json" record "CARD-XREF-RECORD"
cobol_schema CustomerRecord from "../../../examples/cobol/carddemo/cbstm03ab.ir.json" record "CUSTOMER-RECORD"
cobol_schema AccountRecord from "../../../examples/cobol/carddemo/cbstm03ab.ir.json" record "ACCOUNT-RECORD"

theorem trnxRecord_contig : TrnxRecord.Contig := by decide
theorem cardXrefRecord_contig : CardXrefRecord.Contig := by decide
theorem customerRecord_contig : CustomerRecord.Contig := by decide
theorem accountRecord_contig : AccountRecord.Contig := by decide

/-- The bytes of an alphanumeric value. -/
def strOf : FVal → List UInt8
  | .str bs => bs
  | .num _ => []

/-- The integer of a numeric value. -/
def numOf : FVal → Int
  | .num v => v
  | .str _ => 0

end StmBridge

open StmBridge

/-- The transaction file is sorted by card number (`TRNX-CARD-NUM`, byte order). -/
abbrev CardsSorted (trs : List (List UInt8)) : Prop :=
  trs.Pairwise (fun a b => Sem.cmpBytes (tCard a) (tCard b) ≠ .gt)

/-- The domain of `CBSTM03A+B`'s theorems on field values. -/
def Domain (trs xrefs _custs _accts : List (List FVal)) : Prop :=
  trs ≠ [] ∧
  CardsSorted (trs.map TrnxRecord.encode) ∧
  (grp (trs.map TrnxRecord.encode)).length ≤ 50 ∧
  (∀ g ∈ grp (trs.map TrnxRecord.encode), g.length ≤ 10) ∧
  xrefs.length < 10 ^ 5

end EquivLean.Modernize.Cbstm03a
