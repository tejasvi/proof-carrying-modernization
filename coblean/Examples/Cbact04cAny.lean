/-
# CBACT04C for any number of records of one account

One account with any number of category balances (any types, categories, balances), each with
its disclosure group (nonzero or zero rate). CBACT04C ends with `GOBACK`, writes one interest
transaction per category with a nonzero rate, and never `REWRITE`s the account.
-/
import Examples.Cbact04c
open Cobol

namespace CardDemo.Cbact04c

/-- A category balance of the account. -/
structure Cat where
  ty : List UInt8
  cat : Int
  bal : Int
  filler : List UInt8

def Cat.valid (c : Cat) : Prop :=
  c.ty.length = 2 ∧ c.filler.length = 22 ∧ c.cat.natAbs < 10000 ∧ 0 ≤ c.cat ∧
    c.bal.natAbs < 100000000000

/-- Its record in the category-balance file. -/
def Cat.bytes (acct : Int) (c : Cat) : List UInt8 :=
  encodeNum {} TRANCAT_ACCT_ID.fmt acct ++ c.ty ++ encodeNum {} TRANCAT_CD.fmt c.cat ++
    encodeNum {} TRAN_CAT_BAL.fmt c.bal ++ c.filler


/-- Transactions written for the categories `done`: those with a nonzero rate. -/
def nTx (rate : Cat → Int) (done : List Cat) : Nat := (done.filter (fun c => rate c ≠ 0)).length

/-- Eleven EBCDIC spaces (the initial `WS-LAST-ACCT-NUM`). -/
theorem fitNum_total_bound (v : Int) :
    (Sem.fitNum {} { digits := 11, scale := 2, signed := true } v).2.natAbs < 100000000000 := by
  have h := fitNum_holds {} { digits := 11, scale := 2, signed := true } v
  unfold NumFmt.Holds at h
  simp [NumFmt.fullBinary] at h
  omega

def spaces11 : List UInt8 := [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64]

/-- Loop invariant of the main `PERFORM UNTIL END-OF-FILE = 'Y'`: the categories `done` are
processed (`rest`: outcomes of the remaining `READ`s), counters and the current account, its
cross-reference and the running total are in storage, nothing was `REWRITE`n. -/
def Inv (acct : Int) (cats : List Cat) (rate : Cat → Int) (grp xcard : List UInt8)
    (inp0 : List (Nat × List (List UInt8))) (tcat xrefs accts discs : List (List UInt8))
    (rest : List (Option Cat)) (st : State) : Prop :=
  ∃ done todo, cats = done ++ todo ∧
    ((rest = [] ∧ todo = []) ∨ rest = todo.map some ++ [none]) ∧
    st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.clockN = nTx rate done ∧ st.inp = inp0 ∧
    (∃ f1 f2 f4 f3 f5 : FileSt, st.files = [(1, f1), (2, f2), (4, f4), (3, f3), (5, f5)] ∧
      f1.mode = some .input ∧ f1.recs = tcat ∧ f1.pos = done.length ∧ f1.eof = rest.isEmpty ∧
      f2.mode = some .input ∧ f2.recs = xrefs ∧ f4.mode = some .input ∧ f4.recs = discs ∧
      f3.mode = some .io ∧ f3.recs = accts ∧ f5.mode = some .output) ∧
    acctRewrites st = [] ∧ (tranWrites st).length = nTx rate done ∧
    st.mem.size = 1739 ∧
    st.mem.read 1622 1 = (if rest.isEmpty then [232] else [213]) ∧
    st.mem.read 1712 9 = encodeNum {} WS_RECORD_COUNT.fmt done.length ∧
    st.mem.read 1721 6 = encodeNum {} WS_TRANID_SUFFIX.fmt (nTx rate done) ∧
    ((done = [] ∧ st.mem.read 1711 1 = [232] ∧ st.mem.read 1678 11 = spaces11) ∨
     (done ≠ [] ∧ st.mem.read 1711 1 = [213] ∧
      st.mem.read 1678 11 = Sem.digitChars {} 11 acct.natAbs ∧
      st.mem.read 956 11 = encodeNum {} ACCT_ID.fmt acct ∧ st.mem.read 1068 10 = grp ∧
      st.mem.read 852 16 = xcard ∧
      ∃ v, st.mem.read 1700 11 = encodeNum {} WS_TOTAL_INT.fmt v ∧ v.natAbs < 100000000000))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **CBACT04C on one account, any number of category records.**  For every list `cats` of
category-balance records of one account `acct` (any length, any types, categories and
balances), whose account and cross-reference records are found by key and whose disclosure
groups are found (any interest rates, zero included), any initial storage and any clock
readings, CBACT04C ends with `GOBACK`, writes exactly one interest transaction per category
with a nonzero rate, and never `REWRITE`s the account: the interest of the last account in the
file is never posted (the defect reported in CardDemo issue #64), here for inputs of every
length.  Proof: induction over the records (`cobol_loop` with the invariant `Inv`), each
iteration by symbolic execution. -/
theorem cbact04c_one_account (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (acct : Int) (hacct : acct.natAbs < 100000000000) (hacct0 : 0 ≤ acct)
    (cats : List Cat) (hcats : ∀ c ∈ cats, c.valid) (hlen : cats.length < 999999)
    -- the account record and its cross-reference, found by key
    (accts xrefs discs : List (List UInt8)) (ai xi : Nat) (arec xrec : List UInt8)
    (a1 a2 grp af : List UInt8) (abal : Int) (ha1 : a1.length = 1) (ha2 : a2.length = 88)
    (hgrp : grp.length = 10) (haf : af.length = 178)
    (harec : arec = encodeNum {} ACCT_ID.fmt acct ++ a1 ++ encodeNum {} ACCT_CURR_BAL.fmt abal ++
      a2 ++ grp ++ af)
    (hai : Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt acct) accts = some ai)
    (hag : accts.getD ai [] = arec) (hxrec : xrec.length = 50)
    (hxi : Sem.findKey { off := 25, len := 11 } (encodeNum {} FD_XREF_ACCT_ID.fmt acct) xrefs =
      some xi)
    (hxg : xrefs.getD xi [] = xrec)
    -- each category's disclosure group (its rate may be zero)
    (di : Cat → Nat) (rate : Cat → Int) (dfill : Cat → List UInt8)
    (hdisc : ∀ c ∈ cats, Sem.findKey { off := 0, len := 16 }
        (grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di c) ∧
      discs.getD (di c) [] = grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++
        encodeNum {} DIS_INT_RATE.fmt (rate c) ++ dfill c ∧
      (dfill c).length = 28 ∧ (rate c).natAbs < 1000000)
    (n : Nat) (hn : cats.length < n) :
    let r := Cbact04c.run { clock := clk } (n + 60)
      (Cbact04c.initState m [(1, cats.map (Cat.bytes acct)), (2, xrefs), (3, accts), (4, discs)])
    r.1 = .stop .goback ∧ acctRewrites r.2 = [] ∧
      (tranWrites r.2).length = (cats.filter (fun c => rate c ≠ 0)).length := by
  intro r
  simp only [r]
  cobol_sym [hm]
  cobol_loop (Inv acct cats rate grp (xrec.take 16)
      [(1, cats.map (Cat.bytes acct)), (2, xrefs), (3, accts), (4, discs)]
      (cats.map (Cat.bytes acct)) xrefs accts discs) (cats.map some ++ [none])
  · -- after the loop: five CLOSEs, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, rfl,
      ⟨f1, f2, f4, f3, f5, rfl, h1m, -, -, -, h2m, -, h4m, -, h3m, -, h5m⟩, hrw, htw, hsz, heof, -, -, -⟩ :=
      hloopInv
    rcases hrest with ⟨-, rfl⟩ | h
    · simp only [List.append_nil] at hd
      subst hd
      simp only [acctRewrites, tranWrites, nTx, List.filterMap_reverse, List.length_reverse] at hrw htw
      simp only [List.isEmpty_nil, ↓reduceIte] at heof
      cobol_sym [hsz, heof, h1m, h2m, h4m, h3m, h5m]
      simp [acctRewrites, tranWrites, hrw, htw]
    · simp at h
  · -- before the loop: nothing processed, the counters and flags have their VALUEs
    cobol_inv [acctRewrites, tranWrites, nTx, spaces11] with [], cats
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, -, hrest, rfl, rfl, rfl, rfl, rfl, ⟨f1, f2, f4, f3, f5, rfl, -⟩, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_sym [heof]
  · -- one iteration: READ the next category and process it, or reach the end of the file
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, rfl,
        ⟨f1, f2, f4, f3, f5, rfl, h1m, h1r, h1p, h1e, h2m, h2r, h4m, h4r, h3m, h3r, h5m⟩,
        hrw, htw, hsz, heof, hcnt, hsuf, hphase⟩
    rcases hrest with ⟨h, -⟩ | hrest
    · simp at h
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e
    refine ⟨by cobol_auto, ?_⟩
    cases todo with
    | nil =>
      -- the READ reaches the end of the file
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      have hnone : f1.recs[f1.pos]? = none := by rw [h1r, h1p]; simp
      rcases hphase with ⟨rfl, h1711, h1678⟩ | ⟨hd0, h1711, h1678, h956, h1068, h852, v, h1700, hv⟩
      · cobol_auto
        cobol_inv [acctRewrites, tranWrites] with [], []
      · cobol_auto
        cobol_inv [acctRewrites, tranWrites] with cats, [], _, _, _, _, _, v
    | cons c todo' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      obtain ⟨hty, hfill, hcat, hcat0, hbal⟩ := hcats c (by simp)
      obtain ⟨hdi, hdg, hdf, hrate⟩ := hdisc c (by simp)
      have hsome : f1.recs[f1.pos]? = some (Cat.bytes acct c) := by rw [h1r, h1p]; simp
      have hdl : done.length < 999999 := by simp at hlen; omega
      have hntx : nTx rate done < 999999 := by
        have := List.length_filter_le (fun c => decide (rate c ≠ 0)) done
        simp only [nTx]; omega
      obtain ⟨pre, mil, post, hpre, hpost, hmil, hmil0, hck⟩ := hclk (nTx rate done)
      rcases hphase with ⟨rfl, h1711, h1678⟩ | ⟨hd0, h1711, h1678, h956, h1068, h852, v, h1700, hv⟩
      · -- the first category: read the account and its cross-reference
        by_cases hr0 : rate c = 0
        · cobol_auto [Cat.bytes, spaces11, harec]
          cobol_inv [Cat.bytes, acctRewrites, tranWrites, nTx, WS_RECORD_COUNT.fmt] with [c], todo', _, _, _, _, _, 0
        · cobol_auto [Cat.bytes, spaces11, harec]
          cobol_inv [Cat.bytes, acctRewrites, tranWrites, nTx, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt,
            fitNum_total_bound] with [c], todo', _, _, _, _, _,
            (Sem.fitNum {} { digits := 11, scale := 2, signed := true } (divRound .truncation (c.bal * rate c) 120000)).2
      · -- a later category of the same account
        by_cases hr0 : rate c = 0
        · cobol_auto [Cat.bytes, spaces11]
          cobol_inv [Cat.bytes, acctRewrites, tranWrites, nTx, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt]
            with done ++ [c], todo', _, _, _, _, _, v
        · cobol_auto [Cat.bytes, spaces11]
          cobol_inv [Cat.bytes, acctRewrites, tranWrites, nTx, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt,
            fitNum_total_bound] with done ++ [c], todo', _, _, _, _, _,
            (Sem.fitNum {} { digits := 11, scale := 2, signed := true } (v + (Sem.fitNum {} { digits := 11, scale := 2, signed := true } (divRound .truncation (c.bal * rate c) 120000)).2)).2

#print axioms cbact04c_one_account

end CardDemo.Cbact04c
