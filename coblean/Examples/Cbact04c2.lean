/-
# CBACT04C with two accounts: the first is updated exactly, the last not at all

Two category-balance records for two different accounts. CBACT04C posts the first account's
monthly interest `trunc(balance × rate / 1200)` (in cents: `divRound .truncation (bal1 * rate)
120000`) to its balance, zeroes its cycle credit and debit and `REWRITE`s it, writes one
interest transaction per record, and never updates the second (last) account.
-/
import Examples.Cbact04c
open Cobol

namespace CardDemo.Cbact04c

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The first account is updated exactly, the last is not.** For two accounts with one
category balance each (any balances, ids, type, category, nonzero rate, any storage and
clock), CBACT04C ends with `GOBACK`, writes two interest transactions, and `REWRITE`s exactly
one record: account 1 with balance `abal1 + divRound .truncation (bal1 * rate) 120000` and zero
cycle credit and debit. Account 2's interest is written as a transaction but never posted. -/
theorem cbact04c_two_accounts (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    (cpre cpost : List UInt8) (mil : Int) (hcpre : cpre.length = 14) (hcpost : cpost.length = 5)
    (hmil : mil.natAbs < 100) (hmil0 : 0 ≤ mil)
    (hclk0 : clk 0 = cpre ++ encodeNum {} { digits := 2 } mil ++ cpost)
    (hclk1 : clk 1 = cpre ++ encodeNum {} { digits := 2 } mil ++ cpost)
    -- two category-balance records, one per account, same type `ty` and category `cat`
    (acct1 acct2 cat bal1 bal2 : Int) (ty tf1 tf2 : List UInt8) (hty : ty.length = 2)
    (htf1 : tf1.length = 22) (htf2 : tf2.length = 22)
    (hacct1 : acct1.natAbs < 100000000000) (hacct10 : 0 ≤ acct1)
    (hacct2 : acct2.natAbs < 100000000000) (hacct20 : 0 ≤ acct2) (hne : acct1 ≠ acct2)
    (hcat : cat.natAbs < 10000) (hcat0 : 0 ≤ cat)
    (hbal1 : bal1.natAbs < 1000000000) (hbal2 : bal2.natAbs < 1000000000)
    -- account 1 (balance `abal1`, the fields 1050-UPDATE-ACCOUNT touches), account 2, group `grp`
    (s1 mid1 zip1 af1 grp p2 q2 : List UInt8) (abal1 cc1 cd1 : Int)
    (habal1 : abal1.natAbs < 100000000000)
    (hs1 : s1.length = 1) (hmid1 : mid1.length = 54) (hzip1 : zip1.length = 10)
    (haf1 : af1.length = 178) (hgrp : grp.length = 10) (hp2 : p2.length = 101)
    (hq2 : q2.length = 178)
    (card1 card2 cust1 cust2 xf1 xf2 : List UInt8) (hcard1 : card1.length = 16)
    (hcard2 : card2.length = 16) (hcust1 : cust1.length = 9) (hcust2 : cust2.length = 9)
    (hxf1 : xf1.length = 14) (hxf2 : xf2.length = 14)
    (rate : Int) (hrate : rate.natAbs < 1000000) (hr0 : rate ≠ 0) (df : List UInt8)
    (hdf : df.length = 28) (n : Nat) :
    let t1 := encodeNum {} TRANCAT_ACCT_ID.fmt acct1 ++ ty ++ encodeNum {} TRANCAT_CD.fmt cat ++
      encodeNum {} TRAN_CAT_BAL.fmt bal1 ++ tf1
    let t2 := encodeNum {} TRANCAT_ACCT_ID.fmt acct2 ++ ty ++ encodeNum {} TRANCAT_CD.fmt cat ++
      encodeNum {} TRAN_CAT_BAL.fmt bal2 ++ tf2
    let a1 := encodeNum {} ACCT_ID.fmt acct1 ++ s1 ++ encodeNum {} ACCT_CURR_BAL.fmt abal1 ++
      mid1 ++ encodeNum {} ACCT_CURR_CYC_CREDIT.fmt cc1 ++ encodeNum {} ACCT_CURR_CYC_DEBIT.fmt cd1 ++
      zip1 ++ grp ++ af1
    let a2 := encodeNum {} ACCT_ID.fmt acct2 ++ p2 ++ grp ++ q2
    let x1 := card1 ++ cust1 ++ encodeNum {} XREF_ACCT_ID.fmt acct1 ++ xf1
    let x2 := card2 ++ cust2 ++ encodeNum {} XREF_ACCT_ID.fmt acct2 ++ xf2
    let d := grp ++ ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt cat ++ encodeNum {} DIS_INT_RATE.fmt rate ++ df
    let r := Cbact04c.run { clock := clk } (n + 80)
      (Cbact04c.initState m [(1, [t1, t2]), (2, [x1, x2]), (3, [a1, a2]), (4, [d])])
    r.1 = .stop .goback ∧ (tranWrites r.2).length = 2 ∧
      acctRewrites r.2 = [encodeNum {} ACCT_ID.fmt acct1 ++ s1 ++
        encodeNum {} ACCT_CURR_BAL.fmt (abal1 + divRound .truncation (bal1 * rate) 120000) ++ mid1 ++
        encodeNum {} ACCT_CURR_CYC_CREDIT.fmt 0 ++ encodeNum {} ACCT_CURR_CYC_DEBIT.fmt 0 ++
        zip1 ++ grp ++ af1] := by
  have hn1 : acct1.natAbs ≠ acct2.natAbs := fun h => hne (by omega)
  have hn2 : acct2.natAbs ≠ acct1.natAbs := fun h => hne (by omega)
  have hm1 : acct1.natAbs % 100000000000 = acct1.natAbs := Nat.mod_eq_of_lt hacct1
  have hm2 : acct2.natAbs % 100000000000 = acct2.natAbs := Nat.mod_eq_of_lt hacct2
  intro t1 t2 a1 a2 x1 x2 d r
  simp only [r, t1, t2, a1, a2, x1, x2, d]
  cobol_sym [hm, hr0, hne, hn1, hn2, hm1, hm2, hclk0, hclk1, hcpre, hcpost, hty, htf1, htf2, hs1, hmid1, hzip1, haf1, hgrp, hp2,
    hq2, hcard1, hcard2, hcust1, hcust2, hxf1, hxf2, hdf, length_encodeNum, List.length_append,
    List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le]
  rw [loopUntil_succ_before]
  cobol_sym [hm, hr0, hne, hn1, hn2, hm1, hm2, hclk0, hclk1, hcpre, hcpost, hty, htf1, htf2, hs1, hmid1, hzip1, haf1, hgrp, hp2,
    hq2, hcard1, hcard2, hcust1, hcust2, hxf1, hxf2, hdf, length_encodeNum, List.length_append,
    List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le]
  rw [loopUntil_succ_before]
  cobol_sym [hm, hr0, hne, hn1, hn2, hm1, hm2, hclk0, hclk1, hcpre, hcpost, hty, htf1, htf2, hs1, hmid1, hzip1, haf1, hgrp, hp2,
    hq2, hcard1, hcard2, hcust1, hcust2, hxf1, hxf2, hdf, length_encodeNum, List.length_append,
    List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le]
  rw [loopUntil_succ_before]
  cobol_sym [hm, hr0, hne, hn1, hn2, hm1, hm2, hclk0, hclk1, hcpre, hcpost, hty, htf1, htf2, hs1, hmid1, hzip1, haf1, hgrp, hp2,
    hq2, hcard1, hcard2, hcust1, hcust2, hxf1, hxf2, hdf, length_encodeNum, List.length_append,
    List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le]
  rw [loopUntil_succ_before]
  cobol_sym [hm, hr0, hne, hn1, hn2, hm1, hm2, hclk0, hclk1, hcpre, hcpost, hty, htf1, htf2, hs1, hmid1, hzip1, haf1, hgrp, hp2,
    hq2, hcard1, hcard2, hcust1, hcust2, hxf1, hxf2, hdf, length_encodeNum, List.length_append,
    List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le]
  simp [acctRewrites, tranWrites, List.append_assoc]

#print axioms cbact04c_two_accounts

end CardDemo.Cbact04c
