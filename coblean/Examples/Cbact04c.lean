/-
# CardDemo CBACT04C (interest calculator), extracted by the front end

`examples/carddemo/cbact04c.ir.json` is the output of `tools/cobolfe` on `app/cbl/CBACT04C.cbl`
of AWS CardDemo (commit 59cc6c2f, Apache-2.0), unchanged: five indexed and sequential files,
keyed reads by record and alternate key, `FILE STATUS` checks, `COMPUTE`, `STRING`, the clock.
-/
import Cobol
open Cobol

namespace CardDemo

cobol_program Cbact04c from "../examples/carddemo/cbact04c.ir.json"

namespace Cbact04c

/-- Records written to the transaction file (file 5), oldest first. -/
def tranWrites (st : State) : List (List UInt8) :=
  st.out.reverse.filterMap fun | .write 5 bs => some bs | _ => none

/-- `REWRITE`s of account records (file 3). -/
def acctRewrites (st : State) : List (List UInt8) :=
  st.out.reverse.filterMap fun | .rewrite 3 bs => some bs | _ => none

set_option maxRecDepth 20000 in
/-- **The last account's interest is never posted.**  For every input with one category-balance
record (any account, type, category, balance), its account, cross-reference and disclosure group
(any contents, nonzero rate), any initial storage and any clock reading, CBACT04C ends with
`GOBACK`, writes one interest transaction, and never `REWRITE`s the account: the
`ELSE PERFORM 1050-UPDATE-ACCOUNT` branch of the main loop is dead (the loop test exits first),
so the update of the last account in the file is skipped. -/
theorem cbact04c_last_account_not_updated (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
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

#print axioms cbact04c_last_account_not_updated

end Cbact04c
end CardDemo
