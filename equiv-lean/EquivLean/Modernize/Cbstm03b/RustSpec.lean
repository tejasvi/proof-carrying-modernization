import EquivLean.Modernize.Cbstm03b.RustStatement
import EquivLean.Modernize.Cbstm03b.Model

/-!
# CBSTM03B → Rust: the equation of `call`

The translation's state, parameter area and OPEN outcomes as the model's values (`Model.lean`): a file's
records by `rust_record_vals`, its read position by `UScalar.val`, a status item by the code points of its
bytes, an OPEN outcome by its value (`absSt`, `absOe`; the area is `LkM03bArea.vals`).

`CallSpec`: for inputs with the properties that the generated statement's premises give (`CallHyp`), the
translation's `call` does not panic and returns the state and area of `Model.call` on these values.
`RustProof.statement_of_call` derives the generated `Statement` from it.
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbstm03b.Rust

/-- TRNX-FILE as the model's file. -/
def absTrnx (f : cbstm03b.TrnxFile) : Model.FileM :=
  ⟨f.«open», f.recs.val.map FdTrnxfileRec.vals, f.pos.val, f.eof⟩

/-- XREF-FILE as the model's file. -/
def absXref (f : cbstm03b.XrefFile) : Model.FileM :=
  ⟨f.«open», f.recs.val.map FdXreffileRec.vals, f.pos.val, f.eof⟩

/-- CUST-FILE as the model's file. -/
def absCust (f : cbstm03b.CustFile) : Model.FileM :=
  ⟨f.«open», f.recs.val.map FdCustfileRec.vals, f.pos.val, f.eof⟩

/-- ACCT-FILE as the model's file. -/
def absAcct (f : cbstm03b.AcctFile) : Model.FileM :=
  ⟨f.«open», f.recs.val.map FdAcctfileRec.vals, f.pos.val, f.eof⟩

/-- The state kept between calls as the model's state. -/
def absSt (st : cbstm03b.State) : Model.StM where
  trnx := absTrnx st.trnx_file
  xref := absXref st.xref_file
  cust := absCust st.cust_file
  acct := absAcct st.acct_file
  trnxRec := FdTrnxfileRec.vals st.fd_trnxfile_rec
  xrefRec := FdXreffileRec.vals st.fd_xreffile_rec
  custRec := FdCustfileRec.vals st.fd_custfile_rec
  acctRec := FdAcctfileRec.vals st.fd_acctfile_rec
  trnxSt := st.trnxfile_status.val.map (·.val)
  xrefSt := st.xreffile_status.val.map (·.val)
  custSt := st.custfile_status.val.map (·.val)
  acctSt := st.acctfile_status.val.map (·.val)

/-- The OPEN outcomes as the model's: file `id`'s outcome is element `id - 1`. -/
def absOe (oe : Std.Array (Option Std.U8) 4#usize) : Model.OpenErrs :=
  fun id => (oe.val.getD (id - 1) none).map (·.val)

open CardDemo.Cbstm03b (opReadK ddCust ddAcct) in
/-- The properties of a call's inputs that the premises of the generated statement give
(`RustProof.callHyp_of`): every OPEN failure is a two-digit status, the field values are valid for their
schemas, and for a keyed READ (`K`) of CUSTFILE or ACCTFILE the key length is in `1 ..= 25` (coblean's
`cbstm03b_call`) and, for ACCTFILE, the key's first `k` bytes are the CP037 digits `0xF0`–`0xF9` (the
statements' `Domain`). -/
structure CallHyp (oe : Std.Array (Option Std.U8) 4#usize) (st : cbstm03b.State) (q : cbstm03b.LkM03bArea) :
    Prop where
  oe_lt : ∀ i, i < 4 → ∀ c, oe.val.getD i none = some c → c.val < 100
  trnx : ∀ r ∈ st.trnx_file.recs.val, FdTrnxfileRec.Valid (FdTrnxfileRec.vals r)
  xref : ∀ r ∈ st.xref_file.recs.val, FdXreffileRec.Valid (FdXreffileRec.vals r)
  cust : ∀ r ∈ st.cust_file.recs.val, FdCustfileRec.Valid (FdCustfileRec.vals r)
  acct : ∀ r ∈ st.acct_file.recs.val, FdAcctfileRec.Valid (FdAcctfileRec.vals r)
  trnxRec : FdTrnxfileRec.Valid (FdTrnxfileRec.vals st.fd_trnxfile_rec)
  xrefRec : FdXreffileRec.Valid (FdXreffileRec.vals st.fd_xreffile_rec)
  custRec : FdCustfileRec.Valid (FdCustfileRec.vals st.fd_custfile_rec)
  acctRec : FdAcctfileRec.Valid (FdAcctfileRec.vals st.fd_acctfile_rec)
  area : LkM03bArea.Valid (LkM03bArea.vals q)
  keyLn : Model.aOp (LkM03bArea.vals q) = opReadK →
    (Model.aDd (LkM03bArea.vals q) = ddCust ∨ Model.aDd (LkM03bArea.vals q) = ddAcct) →
    1 ≤ Model.aKeyLn (LkM03bArea.vals q) ∧ Model.aKeyLn (LkM03bArea.vals q) ≤ 25
  acctKey : Model.aOp (LkM03bArea.vals q) = opReadK → Model.aDd (LkM03bArea.vals q) = ddAcct →
    ∀ b ∈ (Model.aKey (LkM03bArea.vals q)).take (Model.aKeyLn (LkM03bArea.vals q)).toNat, 240 ≤ b ∧ b ≤ 249

/-- **The equation of `call`**: on inputs with `CallHyp`, the translation returns (no panic) the state and
area of the model's call. -/
def CallSpec : Prop :=
  ∀ (oe : Std.Array (Option Std.U8) 4#usize) (st : cbstm03b.State) (q : cbstm03b.LkM03bArea), CallHyp oe st q →
    ∃ st' q', cbstm03b.call oe st q = .ok (st', q') ∧
      absSt st' = (Model.call (absOe oe) (absSt st) (LkM03bArea.vals q)).1 ∧
      LkM03bArea.vals q' = (Model.call (absOe oe) (absSt st) (LkM03bArea.vals q)).2

end EquivLean.Modernize.Cbstm03b.Rust
