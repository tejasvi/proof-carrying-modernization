import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunDefs
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVR

/-!
# CBTRN02C → Java: the model's posting in the order of the Java code

`Model.St.post` = the category balance update (`postCat`), then the account update (`postAcc`),
then the transaction write (`postTr`), as `postTransaction` calls `updateTcatbal`,
`updateAccount`, `writeTransaction`.
-/

open EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- `2700-UPDATE-TCATBAL` on the model state. -/
def postCat (s : Model.St) (t x : List FV) : Model.St :=
  match Model.findCat s.cats (Model.xAcct x) (Model.tType t) (Model.tCat t) with
  | none =>
    let c : List FV := [.num (Model.xAcct x), .str (Model.tType t), .num (Model.tCat t),
      .num (Model.tAmt t), .str s.catFill]
    { s with cats := s.cats ++ [c],
             disp := s.disp ++ [Model.noCatLine (Model.xAcct x) (Model.tType t) (Model.tCat t)],
             catW := s.catW ++ [c] }
  | some c =>
    let c' := c.set 3 (.num (Cobol.Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt
      (Model.cBal c + Model.tAmt t)).2)
    { s with cats := Model.replaceFirst (Model.catKey (Model.xAcct x) (Model.tType t) (Model.tCat t)) c' s.cats,
             catFill := Model.cFill c, catRW := s.catRW ++ [c'] }

/-- `2800-UPDATE-ACCOUNT-REC` on the model state. -/
def postAcc (s : Model.St) (t a : List FV) : Model.St :=
  { s with accts := Model.replaceFirst (fun b => Model.aId b == Model.aId a)
             (Model.postAcct a (Model.tAmt t)) s.accts,
           acctRW := s.acctRW ++ [Model.postAcct a (Model.tAmt t)] }

/-- `2900-WRITE-TRANSACTION-FILE` on the model state. -/
def postTr (s : Model.St) (t : List FV) (clk : List UInt8) : Model.St :=
  { s with tranW := s.tranW ++ [Model.tranVals t clk], posted := s.posted + 1 }

theorem post_eq (clk : List UInt8) (s : Model.St) (t x a : List FV) :
    Model.St.post clk s t x a = postTr (postAcc (postCat s t x) t a) t clk := by
  unfold Model.St.post postCat postAcc postTr
  cases Model.findCat s.cats (Model.xAcct x) (Model.tType t) (Model.tCat t) <;> rfl

end EquivLean.Modernize.Cbtrn02c.Java
