import EquivLean.Demo.Gen.Aeneas.Cbact04c.Types

/-!
# CBACT04C in Rust: the main loop of `run` as a fold over integers

`examples/rust/cbact04c/src/lib.rs` (Charon + Aeneas, `EquivLean.Demo.Gen.Aeneas.Cbact04c.Funs`, a copy of
`EquivLean/Demo/Gen/Aeneas/Cbact04c/Funs.lean`).  This file has

* `RCat`/`RAcct`: the records with the values of their Rust fields (`i64`, `i32` as `Int`;
  the keys `u16`, `u128` as `Nat`), and `RCat.ofRust`/`RAcct.ofRust`;
* `rStep`/`rRun`: one iteration of the main loop of `run` and the whole loop, over the records,
  with the account and rate lookups `acctOf`, `rateOf`, as the Java model `jRun`
  (`EquivLean.Demo.Cbact04c.jRun`) but on integers: within the PIC bounds the checked `i64`
  operations of the Rust code are exact, and Rust's `/` and `%` on `i64` are `Int.tdiv` and
  `Int.tmod` (truncation toward zero).
-/

namespace EquivLean.Demo.Cbact04cRust

/-- A category-balance record (TRAN-CAT-BAL-RECORD): account id, type code (the big-endian
value of its two bytes), category code, balance in cents. -/
structure RCat where
  acct : Int
  ty : Nat
  cat : Int
  bal : Int

/-- An account record: the fields the program reads or changes (the group id is the big-endian
value of its ten bytes). -/
structure RAcct where
  id : Int
  bal : Int
  cc : Int
  cd : Int
  grp : Nat
  deriving Inhabited, DecidableEq

/-- The values of a Rust `Cat`. -/
def RCat.ofRust (c : cbact04c.Cat) : RCat := ⟨c.acct_id.val, c.type_cd.val, c.cat_cd.val, c.bal.val⟩

/-- The values of a Rust `Account`. -/
def RAcct.ofRust (a : cbact04c.Account) : RAcct :=
  ⟨a.id.val, a.bal.val, a.cyc_credit.val, a.cyc_debit.val, a.group_id.val⟩

/-! ## The main loop of `run` -/

/-- State of the main loop: the rewrites so far (in order), the transaction count,
`first_time`, `last_acct`, `total_int` and the current account. -/
structure RState where
  rewrites : List RAcct
  tx : Nat
  first : Bool
  last : Int
  total : Int
  acct : RAcct

/-- `post(a, t)`: interest posted, cycle credit and debit zero (`S9(10)V99`: `% 10^12`). -/
def rPost (a : RAcct) (t : Int) : RAcct :=
  ⟨a.id, (a.bal + t).tmod 1000000000000, 0, 0, a.grp⟩

/-- One iteration on the record `c`, with the account and rate lookups `acctOf`, `rateOf`. -/
def rStep (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int) (s : RState) (c : RCat) :
    RState :=
  let s1 : RState :=
    if s.first || c.acct != s.last then
      { rewrites := if s.first then s.rewrites else s.rewrites ++ [rPost s.acct s.total],
        tx := s.tx, first := false, last := c.acct, total := 0, acct := acctOf c.acct }
    else s
  let r := rateOf s1.acct.grp c.ty c.cat
  if r = 0 then s1
  else { s1 with total := (s1.total + ((c.bal * r).tdiv 120000).tmod 100000000000).tmod 100000000000,
                 tx := s1.tx + 1 }

def rInit : RState := ⟨[], 0, true, 0, 0, default⟩

/-- The account-change part of `rStep`. -/
def rChg (acctOf : Int → RAcct) (s : RState) (c : RCat) : RState :=
  if s.first || c.acct != s.last then
    { rewrites := if s.first then s.rewrites else s.rewrites ++ [rPost s.acct s.total],
      tx := s.tx, first := false, last := c.acct, total := 0, acct := acctOf c.acct }
  else s

/-- The rate part of `rStep`. -/
def rRate (rateOf : Nat → Nat → Int → Int) (s1 : RState) (c : RCat) : RState :=
  if rateOf s1.acct.grp c.ty c.cat = 0 then s1
  else { s1 with total := (s1.total + ((c.bal * rateOf s1.acct.grp c.ty c.cat).tdiv 120000).tmod
                    100000000000).tmod 100000000000,
                 tx := s1.tx + 1 }

theorem rStep_eq (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int) (s : RState) (c : RCat) :
    rStep acctOf rateOf s c = rRate rateOf (rChg acctOf s c) c := rfl

/-- The loop over all records. -/
def rRun (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int) (cs : List RCat) : RState :=
  cs.foldl (rStep acctOf rateOf) rInit

end EquivLean.Demo.Cbact04cRust
