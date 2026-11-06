/-
# CBACT04C, paragraph by paragraph

Summaries of the two lookups of the main loop, `1100-GET-ACCT-DATA` (account by record key)
and `1110-GET-XREF-DATA` (cross-reference by alternate key), proved once for any program `P`
with CBACT04C's configuration and files, then used by symbolic execution wherever the
paragraphs run: `cbact04c_last_account_not_updated'` is the one-account theorem with both
lookups taken from their summaries.  The summaries are derived (`cobol_summary`): only the
paragraph, the shape of the state and the hypotheses are written; the paragraph's effect is
computed by symbolic execution and printed.  The record number `i` of each keyed read is a
plain variable: at a call site the side condition `Sem.findKey … = some ?i` is rewritten with
the call site's facts and assigns it.
-/
import Examples.Cbact04c
open Cobol

namespace CardDemo.Cbact04c

/-- The account file state `1100-GET-ACCT-DATA` reads from (opened `I-O`). -/
abbrev acctFile (accts : List (List UInt8)) (p : Nat) (e : Bool) (c : Option Nat) : FileSt :=
  { mode := some .io, recs := accts, pos := p, eof := e, cur := c }

/-- The cross-reference file state `1110-GET-XREF-DATA` reads from. -/
abbrev xrefFile (xrefs : List (List UInt8)) (p : Nat) (e : Bool) (c : Option Nat) : FileSt :=
  { mode := some .input, recs := xrefs, pos := p, eof := e, cur := c }

/-- **Summary of `1100-GET-ACCT-DATA`** (derived by `cobol_summary`: the right-hand side is
computed, not written): the account whose key is in `FD-ACCT-ID` is record `i`; it is read into
the record area and `ACCOUNT-RECORD`, `ACCTFILE-STATUS` is `'00'`, `APPL-RESULT` 0. -/
cobol_summary getAcct_found (P : Program) (hcfg : P.cfg = Cbact04c.cfg)
    (hfiles : P.files = Cbact04c.files) (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat)
    (m : Mem) (hm : m.size = 1739) (idx : List (Nat × Int)) (slots : List (ExitPt × Nat))
    (saves : List (Nat × Nat)) (active : List Nat) (out : List Event)
    (inp : List (Nat × List (List UInt8))) (clockN : Nat) (f1 f2 f4 f5 : FileSt)
    (accts : List (List UInt8)) (p3 : Nat) (e3 : Bool) (c3 : Option Nat) (i : Nat)
    (hi : Sem.findKey { off := 0, len := 11 } (m.read 150 11) accts = some i)
    (hrec : (accts.getD i []).length = 300) :
    Sem.execSentences P env rec fuel Cbact04c.«1100-GET-ACCT-DATA».body
      ⟨m, idx, slots, saves, active, out, inp,
        [(1, f1), (2, f2), (4, f4), (3, acctFile accts p3 e3 c3), (5, f5)], clockN⟩
  using [hcfg, hfiles, hm, hi, hrec]

/-- **Summary of `1110-GET-XREF-DATA`** (derived): the cross-reference whose alternate key is
the account number in `FD-XREF-ACCT-ID` is record `i`; it is read into `CARD-XREF-RECORD`. -/
cobol_summary getXref_found (P : Program) (hcfg : P.cfg = Cbact04c.cfg)
    (hfiles : P.files = Cbact04c.files) (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat)
    (m : Mem) (hm : m.size = 1739) (idx : List (Nat × Int)) (slots : List (ExitPt × Nat))
    (saves : List (Nat × Nat)) (active : List Nat) (out : List Event)
    (inp : List (Nat × List (List UInt8))) (clockN : Nat) (f1 f3 f4 f5 : FileSt)
    (xrefs : List (List UInt8)) (p2 : Nat) (e2 : Bool) (c2 : Option Nat) (i : Nat)
    (hi : Sem.findKey { off := 25, len := 11 } (m.read 75 11) xrefs = some i)
    (hrec : (xrefs.getD i []).length = 50) :
    Sem.execSentences P env rec fuel Cbact04c.«1110-GET-XREF-DATA».body
      ⟨m, idx, slots, saves, active, out, inp,
        [(1, f1), (2, xrefFile xrefs p2 e2 c2), (4, f4), (3, f3), (5, f5)], clockN⟩
  using [hcfg, hfiles, hm, hi, hrec]

-- the lookups are taken from their summaries wherever they run
attribute [local cobol_eval high] getAcct_found getXref_found

set_option maxRecDepth 20000 in
/-- **The last account's interest is never posted** (lookups by their summaries).  For every input with one category-balance
record (any account, type, category, balance), its account, cross-reference and disclosure group
(any contents, nonzero rate), any initial storage and any clock reading, CBACT04C ends with
`GOBACK`, writes one interest transaction, and never `REWRITE`s the account: the
`ELSE PERFORM 1050-UPDATE-ACCOUNT` branch of the main loop is dead (the loop test exits first),
so the update of the last account in the file is skipped. -/
theorem cbact04c_last_account_not_updated' (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    -- the clock reading: `YYYYMMDDhhmmss`, hundredths `mil` (two digits), time zone
    (cpre cpost : List UInt8) (mil : Int) (hcpre : cpre.length = 14) (hcpost : cpost.length = 5)
    (hmil : mil.natAbs < 100) (hmil0 : 0 ≤ mil)
    (hclk : clk 0 = cpre ++ encodeNum {} { digits := 2 } mil ++ cpost)
    -- the one category-balance record: account `acct`, type `ty`, category `cat`, balance `bal`
    (acct cat bal : Int) (ty tf : List UInt8) (hty : ty.length = 2) (htf : tf.length = 22)
    (hacct : acct.natAbs < 100000000000) (hacct0 : 0 ≤ acct) (hcat : cat.natAbs < 10000)
    (hcat0 : 0 ≤ cat)
    (hbal : bal.natAbs < 100000000000)
    -- the account, its cross-reference and its disclosure group
    (a1 a2 grp af : List UInt8) (abal : Int)
    (ha1 : a1.length = 1) (ha2 : a2.length = 88) (hgrp : grp.length = 10)
    (haf : af.length = 178)
    (card cust xf : List UInt8) (hcard : card.length = 16) (hcust : cust.length = 9)
    (hxf : xf.length = 14)
    (rate : Int) (hrate : rate.natAbs < 1000000) (hr0 : rate ≠ 0) (df : List UInt8)
    (hdf : df.length = 28) (n : Nat) :
    let t := encodeNum {} TRANCAT_ACCT_ID.fmt acct ++ ty ++ encodeNum {} TRANCAT_CD.fmt cat ++
      encodeNum {} TRAN_CAT_BAL.fmt bal ++ tf
    let a := encodeNum {} ACCT_ID.fmt acct ++ a1 ++ encodeNum {} ACCT_CURR_BAL.fmt abal ++ a2 ++
      grp ++ af
    let x := card ++ cust ++ encodeNum {} XREF_ACCT_ID.fmt acct ++ xf
    let d := grp ++ ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt cat ++ encodeNum {} DIS_INT_RATE.fmt rate ++ df
    let r := Cbact04c.run { clock := clk } (n + 60)
      (Cbact04c.initState m [(1, [t]), (2, [x]), (3, [a]), (4, [d])])
    r.1 = .stop .goback ∧ acctRewrites r.2 = [] ∧ (tranWrites r.2).length = 1 := by
  intro t a x d r
  simp only [r, t, a, x, d]
  -- up to the main loop, then its iterations (the record, end of file, the exit test), then the
  -- closing paragraphs
  cobol_sym [hm, hr0, hclk, hcpre, hcpost, hty, htf, ha1, ha2, hgrp, haf, hcard, hcust, hxf, hdf, length_encodeNum,
    List.length_append, List.take_append, List.drop_append, List.take_of_length_le,
    List.drop_of_length_le]
  rw [loopUntil_succ]
  cobol_sym [hm, hr0, hclk, hcpre, hcpost, hty, htf, ha1, ha2, hgrp, haf, hcard, hcust, hxf, hdf, length_encodeNum,
    List.length_append, List.take_append, List.drop_append, List.take_of_length_le,
    List.drop_of_length_le]
  rw [loopUntil_succ]
  cobol_sym [hm, hr0, hclk, hcpre, hcpost, hty, htf, ha1, ha2, hgrp, haf, hcard, hcust, hxf, hdf, length_encodeNum,
    List.length_append, List.take_append, List.drop_append, List.take_of_length_le,
    List.drop_of_length_le]
  rw [loopUntil_succ]
  cobol_sym [hm, hr0, hclk, hcpre, hcpost, hty, htf, ha1, ha2, hgrp, haf, hcard, hcust, hxf, hdf, length_encodeNum,
    List.length_append, List.take_append, List.drop_append, List.take_of_length_le,
    List.drop_of_length_le]
  simp [acctRewrites, tranWrites]

#print axioms cbact04c_last_account_not_updated'

-- the proof uses both summaries
open Lean Meta in
#eval show MetaM (Bool × Bool) from do
  let some (.thmInfo i) := (← getEnv).find? `CardDemo.Cbact04c.cbact04c_last_account_not_updated'
    | return (false, false)
  let cs := i.value.getUsedConstants
  return (cs.contains `CardDemo.Cbact04c.getAcct_found, cs.contains `CardDemo.Cbact04c.getXref_found)

end CardDemo.Cbact04c
