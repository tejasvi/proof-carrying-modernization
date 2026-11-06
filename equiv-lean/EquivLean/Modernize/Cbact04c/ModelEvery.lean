import EquivLean.Modernize.Cbact04c.Model

/-!
# CBACT04C on every input: the error paths and the `DEFAULT` disclosure group

As `Model.run`, on every input, as the translations do (Rust `lib.rs` `process_record`, `abend`,
`update_account`, `run`; Java `mod_cbact04c`):
- a missing account or cross-reference: `ACCOUNT NOT FOUND: ` and the 11-digit id, the error
  line, `FILE STATUS IS: NNNN0023`, `ABENDING PROGRAM`, and the run stops (no end line);
- a missing disclosure group: `DISCLOSURE GROUP RECORD MISSING`, `TRY WITH DEFAULT GROUP CODE`,
  then the group `DEFAULT   `; a missing `DEFAULT` group abends the same way;
- the previous account is rewritten before the lookups of a new account (also when they fail);
- the last account is not rewritten at the end (CardDemo issue #64).
When every lookup succeeds, `runE` is `run` (with `abended = false`).
-/

open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Model

/-! ## The lookups (first match, if any) -/

def findAcctO (accts : List (List FVal)) (id : Int) : Option (List FVal) :=
  accts.find? (fun a => aId a == id)

def findXrefO (xrefs : List (List FVal)) (id : Int) : Option (List FVal) :=
  xrefs.find? (fun x => xAcct x == id)

def findRateO (discs : List (List FVal)) (grp ty : List UInt8) (cat : Int) : Option Int :=
  (discs.find? (fun d => dGrp d == grp && dType d == ty && dCat d == cat)).map dRate

/-- `DEFAULT   ` (EBCDIC): the group of the default disclosure records. -/
def defaultGrp : List UInt8 := [196, 197, 198, 193, 228, 211, 227, 64, 64, 64]

/-! ## The run -/

/-- The translations' state between two category records, and whether the run has abended. -/
structure StE where
  accts : List (List FVal)
  lastId : Option Int
  acct : List FVal
  xref : List FVal
  total : Int
  k : Nat
  disp : List (List Nat)
  writes : List (List FVal)
  rewrites : List (List FVal)
  stop : Bool

/-- An abend after a failed keyed read (`9999-ABEND-PROGRAM` after `9910-DISPLAY-IO-STATUS`
with status 23): the lines, the file status, `ABENDING PROGRAM`. -/
def StE.abend (s : StE) (lines : List (List Nat)) : StE :=
  { s with disp := s.disp ++ lines ++ [txt "FILE STATUS IS: NNNN0023", txt "ABENDING PROGRAM"],
           stop := true }

/-- The interest of record `t` at rate `rate` (`1300-COMPUTE-INTEREST`, `1300-B-WRITE-TX`). -/
def StE.interest (parm clk : List UInt8) (s : StE) (t : List FVal) (rate : Int) : StE :=
  if rate = 0 then s
  else
    let amt := Int.tmod (Int.tdiv (tBal t * rate) 120000) (10 ^ 11)
    let k := (s.k + 1) % 1000000
    { s with total := Int.tmod (s.total + amt) (10 ^ 11), k,
             writes := s.writes ++ [tranVals parm clk k (aId s.acct) (xCard s.xref) amt] }

/-- The rate of record `t` (`1200-GET-INTEREST-RATE`, `1200-A-GET-DEFAULT-INT-RATE`), then the
interest. -/
def StE.rate (discs : List (List FVal)) (parm clk : List UInt8) (s : StE) (t : List FVal) : StE :=
  match findRateO discs (aGrp s.acct) (tType t) (tCat t) with
  | some r => s.interest parm clk t r
  | none =>
    let s1 : StE := { s with disp := s.disp ++ [txt "DISCLOSURE GROUP RECORD MISSING",
      txt "TRY WITH DEFAULT GROUP CODE"] }
    match findRateO discs defaultGrp (tType t) (tCat t) with
    | some r => s1.interest parm clk t r
    | none => s1.abend [txt "ERROR READING DEFAULT DISCLOSURE GROUP"]

/-- One category record `t`: `DISPLAY` it; on a change of account, `REWRITE` the previous one
(not before the first) and read the new account and its cross-reference (an abend if one is
missing); then the rate and the interest. Nothing after an abend. -/
def stepE (xrefs discs : List (List FVal)) (parm clk : List UInt8) (s : StE) (t : List FVal) : StE :=
  if s.stop then s
  else
    let s1 : StE := { s with disp := s.disp ++ [TranCatBalRecord.textS t] }
    if s1.lastId = some (tAcct t) then s1.rate discs parm clk t
    else
      let p := posted s1.acct s1.total
      let s2 : StE :=
        if s1.lastId.isSome then
          { s1 with accts := replaceFirst (fun a => aId a == aId s1.acct) p s1.accts,
                    rewrites := s1.rewrites ++ [p] }
        else s1
      match findAcctO s2.accts (tAcct t) with
      | none => s2.abend [txt "ACCOUNT NOT FOUND: " ++ zpad 11 (tAcct t).natAbs,
          txt "ERROR READING ACCOUNT FILE"]
      | some a =>
        match findXrefO xrefs (tAcct t) with
        | none => s2.abend [txt "ACCOUNT NOT FOUND: " ++ zpad 11 (tAcct t).natAbs,
            txt "ERROR READING XREF FILE"]
        | some x =>
          ({ s2 with lastId := some (tAcct t), total := 0, acct := a, xref := x } : StE).rate
            discs parm clk t

/-- The state before the first record. -/
def initE (accts : List (List FVal)) : StE :=
  { accts, lastId := none, acct := [], xref := [], total := 0, k := 0,
    disp := [txt "START OF EXECUTION OF PROGRAM CBACT04C"], writes := [], rewrites := [],
    stop := false }

/-- The outputs, and whether the run abended. -/
structure OutE where
  disp : List (List Nat)
  writes : List (List FVal)
  rewrites : List (List FVal)
  abended : Bool

/-- **What CBACT04C outputs on every input.** -/
def runE (tcat xrefs accts discs : List (List FVal)) (parm clk : List UInt8) : OutE :=
  let s := tcat.foldl (stepE xrefs discs parm clk) (initE accts)
  { disp := if s.stop then s.disp else s.disp ++ [txt "END OF EXECUTION OF PROGRAM CBACT04C"],
    writes := s.writes, rewrites := s.rewrites, abended := s.stop }

end EquivLean.Modernize.Cbact04c.Model
