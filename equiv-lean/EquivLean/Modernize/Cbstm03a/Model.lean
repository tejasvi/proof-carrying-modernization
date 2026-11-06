import EquivLean.Modernize.Cbstm03a.Domain
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Trans

/-!
# CBSTM03A: Field-value model of the statement generator

Factors the per-block statement and HTML helpers (`modelHeadStmt`, `modelHeadHtml`,
`modelTranStmt`, `modelTranHtml`, `modelAddAmt`, `modelTailStmt`, `modelTailHtml`) and defines
`Model.run trs xrefs custs accts : Out` over the input field values.
-/

open Cobol Cobol.StmCore EquivLean.Cobol.Rec EquivLean.Modernize.Cbstm03a.StmBridge

namespace EquivLean.Modernize.Cbstm03a.Model

/-- The outputs of a `CBSTM03A` run (as CP037 code points, after dropping the 11 constant
`PSA`/`TCB`/`TIOT` walk `DISPLAY` lines). -/
structure Out where
  disp : List (List Nat)
  stmtWrites : List (List Nat)
  htmlWrites : List (List Nat)
  abended : Bool
  deriving DecidableEq, Repr

/-! ## Per-block helpers -/

/-- The 16 `STMT-FILE` header lines for customer `c` and account `a` (as CP037 code points). -/
def modelHeadStmt (c a : List FVal) : List (List Nat) :=
  (stmtHead (stName (strOf (c.getD 1 default)) (strOf (c.getD 2 default)) (strOf (c.getD 3 default)))
    (strOf (c.getD 4 default)) (strOf (c.getD 5 default))
    (stAdd3 (strOf (c.getD 6 default)) (strOf (c.getD 7 default))
      (strOf (c.getD 8 default)) (strOf (c.getD 9 default)))
    (stAcctId (numOf (a.getD 0 default)))
    (edit9 (numOf (a.getD 2 default)))
    (stFico (numOf (c.getD 17 default)))).map (·.map cp037Code)

/-- The 56 `HTML-FILE` header lines for customer `c` and account `a` (as CP037 code points). -/
def modelHeadHtml (c a : List FVal) : List (List Nat) :=
  (htmlHead (stName (strOf (c.getD 1 default)) (strOf (c.getD 2 default)) (strOf (c.getD 3 default)))
    (strOf (c.getD 4 default)) (strOf (c.getD 5 default))
    (stAdd3 (strOf (c.getD 6 default)) (strOf (c.getD 7 default))
      (strOf (c.getD 8 default)) (strOf (c.getD 9 default)))
    (stAcctId (numOf (a.getD 0 default)))
    (edit9 (numOf (a.getD 2 default)))
    (stFico (numOf (c.getD 17 default)))).map (·.map cp037Code)

/-- One `STMT-FILE` transaction detail line for transaction `r` (as CP037 code points). -/
def modelTranStmt (r : List FVal) : List Nat :=
  (tranStmt (strOf (r.getD 1 default)) (strOf (r.getD 5 default))
    (editZ (numOf (r.getD 6 default)))).map cp037Code

/-- The `HTML-FILE` transaction detail lines for transaction `r` (as CP037 code points). -/
def modelTranHtml (r : List FVal) : List (List Nat) :=
  (tranHtml (strOf (r.getD 1 default)) (strOf (r.getD 5 default))
    (editZ (numOf (r.getD 6 default)))).map (·.map cp037Code)

/-- `ADD TRNX-AMT TO WS-TOTAL-AMT` (`PIC S9(9)V99 COMP-3` high-order truncation). -/
def modelAddAmt (acc : Int) (r : List FVal) : Int :=
  (Sem.fitNum {} { digits := 11, scale := 2, signed := true, usage := .packed }
    (acc + numOf (r.getD 6 default))).2

/-- The 3 closing `STMT-FILE` lines for total amount `total` (as CP037 code points). -/
def modelTailStmt (total : Int) : List (List Nat) :=
  (tailStmt total).map (·.map cp037Code)

/-- The 8 closing `HTML-FILE` lines (as CP037 code points). -/
def modelTailHtml : List (List Nat) :=
  tailHtml.map (·.map cp037Code)

/-- The transactions of card `card` in file order. -/
def ofCardF (card : List UInt8) (trs : List (List FVal)) : List (List FVal) :=
  trs.filter (fun r => strOf (r.getD 0 default) == card)

/-- All `STMT-FILE` lines written for one cross-reference record with customer `c` and account `a`. -/
def modelStmtOf (trs : List (List FVal)) (card : List UInt8) (c a : List FVal) : List (List Nat) :=
  let ts := ofCardF card trs
  modelHeadStmt c a ++ (ts.map modelTranStmt ++ modelTailStmt (ts.foldl modelAddAmt 0))

/-- All `HTML-FILE` lines written for one cross-reference record with customer `c` and account `a`. -/
def modelHtmlOf (trs : List (List FVal)) (card : List UInt8) (c a : List FVal) : List (List Nat) :=
  let ts := ofCardF card trs
  modelHeadHtml c a ++ (ts.flatMap modelTranHtml ++ modelTailHtml)

/-- The 3 `DISPLAY` lines emitted when a customer lookup fails (oldest first, as CP037 code points). -/
def modelCustAbortDisp : List (List Nat) :=
  [ ([197, 217, 217, 214, 217, 64, 217, 197, 193, 196, 201, 213, 199, 64,
      195, 228, 226, 227, 198, 201, 211, 197] : List UInt8).map cp037Code,
    ([217, 197, 227, 228, 217, 213, 64, 195, 214, 196, 197, 122, 64, 242, 243] : List UInt8).map cp037Code,
    ([193, 194, 197, 213, 196, 201, 213, 199, 64, 215, 217, 214, 199, 217, 193, 212] : List UInt8).map cp037Code ]

/-- The 3 `DISPLAY` lines emitted when an account lookup fails (oldest first, as CP037 code points). -/
def modelAcctAbortDisp : List (List Nat) :=
  [ ([197, 217, 217, 214, 217, 64, 217, 197, 193, 196, 201, 213, 199, 64,
      193, 195, 195, 227, 198, 201, 211, 197] : List UInt8).map cp037Code,
    ([217, 197, 227, 228, 217, 213, 64, 195, 214, 196, 197, 122, 64, 242, 243] : List UInt8).map cp037Code,
    ([193, 194, 197, 213, 196, 201, 213, 199, 64, 215, 217, 214, 199, 217, 193, 212] : List UInt8).map cp037Code ]

/-- Iterate over `xrefs`, accumulating `stmtWrites` and `htmlWrites` until EOF or a missing
customer/account key. -/
def loop (trs custs accts : List (List FVal)) :
    List (List FVal) → List (List Nat) → List (List Nat) → Out
  | [], stmts, htmls => ⟨[], stmts, htmls, false⟩
  | x :: xs, stmts, htmls =>
    let card := strOf (x.getD 0 default)
    let cid := numOf (x.getD 1 default)
    let aid := numOf (x.getD 2 default)
    match custs.find? (fun c => numOf (c.getD 0 default) == cid) with
    | none => ⟨modelCustAbortDisp, stmts, htmls, true⟩
    | some c =>
      match accts.find? (fun a => numOf (a.getD 0 default) == aid) with
      | none => ⟨modelAcctAbortDisp, stmts, htmls, true⟩
      | some a =>
        loop trs custs accts xs
          (stmts ++ modelStmtOf trs card c a)
          (htmls ++ modelHtmlOf trs card c a)

/-- **Field-value model of `CBSTM03A`.** -/
def run (trs xrefs custs accts : List (List FVal)) : Out :=
  loop trs custs accts xrefs [] []

end EquivLean.Modernize.Cbstm03a.Model
