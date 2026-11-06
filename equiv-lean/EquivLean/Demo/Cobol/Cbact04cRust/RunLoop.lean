import EquivLean.Demo.Cobol.Cbact04cRust.RunDefs

/-!
# The Rust `run` returns the rewrites and the count of the fold `rRun` (no panic)

`run_eq`: on inputs satisfying `RunPre` (each category record's account and disclosure group
found by key, the field bounds, at most `u32::MAX` records), the Aeneas translation of
`cbact04c::run` returns `ok (rewrites, count)`: no panic (every checked operation is in range,
every lookup finds its key, `unwrap`/`expect` see `Some`), with `rewrites` the posted accounts of
`rRun` and `count` its transaction count.

Proof: `loop.spec_decr_nat` (Aeneas' loop rule, variant `len - i`) with the invariant `Inv`: the
Rust loop state and the model state after the same records agree, and the rest of the fold
reaches `rRun`.  One iteration (`body_spec`): the account-change part by rewriting with the
callee equations of `Cbact04cRust/RunDefs.lean` (first record, same account, account change: `post` and
`push`), then the rate part by Aeneas' `step*`; its two leaves (zero or nonzero rate) are
`inv_rate_zero` and `inv_rate_nz`, from the facts `Mid` common to the three cases.
-/

open Aeneas Aeneas.Std Result

namespace EquivLean.Demo.Cbact04cRust
open cbact04c

/-- The loop invariant: the Rust loop state `(rw, tx, first, last, total, acct, i)` and the
model state `m` after the records `cats[0..i)` agree; after the first record the current
account is the one read for `last`, a key of a record read; the bounds; the rest of the fold
reaches `rRun`. -/
def Inv (cats : Slice Cat) (accounts : Slice Account) (acctOf : Int → RAcct)
    (rateOf : Nat → Nat → Int → Int) (rw : alloc.vec.Vec Account) (tx : Std.U32) (first : Bool)
    (last total : Std.I64) (acct : Option Account) (i : Std.Usize) (m : RState) : Prop :=
  rw.val.map RAcct.ofRust = m.rewrites ∧ tx.val = m.tx ∧ first = m.first ∧ last.val = m.last ∧
  total.val = m.total ∧ i.val ≤ cats.val.length ∧ m.rewrites.length ≤ i.val ∧ m.tx ≤ i.val ∧
  m.total.natAbs < 100000000000 ∧
  (first = false → acct = accounts.val.find? (acctKey last) ∧ m.acct = acctOf last.val ∧
    ∃ c ∈ cats.val, c.acct_id = last) ∧
  ((cats.val.drop i.val).map RCat.ofRust).foldl (rStep acctOf rateOf) m =
    rRun acctOf rateOf (cats.val.map RCat.ofRust)

/-- The result of `run`: the rewrites and the count of `rRun`. -/
def RunPost (cats : Slice Cat) (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)
    (r : alloc.vec.Vec Account × Std.U32) : Prop :=
  r.1.val.map RAcct.ofRust = (rRun acctOf rateOf (cats.val.map RCat.ofRust)).rewrites ∧
  r.2.val = (rRun acctOf rateOf (cats.val.map RCat.ofRust)).tx

/-- The invariant on the loop state tuple. -/
def InvS (cats : Slice Cat) (accounts : Slice Account) (acctOf : Int → RAcct)
    (rateOf : Nat → Nat → Int → Int)
    (s : alloc.vec.Vec Account × Std.U32 × Bool × Std.I64 × Std.I64 × Option Account × Std.Usize) :
    Prop :=
  ∃ m, Inv cats accounts acctOf rateOf s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1
    s.2.2.2.2.2.2 m

theorem tmod_bound11 (x : Int) : (x.tmod 100000000000).natAbs < 100000000000 := by
  rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by decide)

/-- The loop state after the account-change part of an iteration on the record `c = cats[i]`:
the Rust values `(rw1, tx, last1, total1, acct1)` and the model state `s1` agree. -/
structure Mid (cats : Slice Cat) (accounts : Slice Account) (acctOf : Int → RAcct)
    (rateOf : Nat → Nat → Int → Int) (c : Cat) (i : Std.Usize) (s1 : RState)
    (rw1 : alloc.vec.Vec Account) (tx : Std.U32) (last1 total1 : Std.I64) (acct1 : Option Account) :
    Prop where
  rw : rw1.val.map RAcct.ofRust = s1.rewrites
  tx : tx.val = s1.tx
  first : s1.first = false
  last : last1.val = s1.last
  total : total1.val = s1.total
  lt : i.val < cats.val.length
  rwl : s1.rewrites.length ≤ i.val + 1
  txl : s1.tx ≤ i.val
  tb : s1.total.natAbs < 100000000000
  acct : acct1 = accounts.val.find? (acctKey last1)
  sacct : s1.acct = acctOf last1.val
  lastc : ∃ c' ∈ cats.val, c'.acct_id = last1
  fold : ((cats.val.drop (i.val + 1)).map RCat.ofRust).foldl (rStep acctOf rateOf)
    (rRate rateOf s1 (RCat.ofRust c)) = rRun acctOf rateOf (cats.val.map RCat.ofRust)

section
variable {cats : Slice Cat} {accounts : Slice Account} {acctOf : Int → RAcct}
  {rateOf : Nat → Nat → Int → Int} {c : Cat} {i : Std.Usize} {s1 : RState}
  {rw1 : alloc.vec.Vec Account} {tx : Std.U32} {last1 total1 : Std.I64} {acct1 : Option Account}

/-- The end of an iteration with a zero rate. -/
theorem inv_rate_zero (hm : Mid cats accounts acctOf rateOf c i s1 rw1 tx last1 total1 acct1)
    (rate : Std.I64) (hrate : rate.val = rateOf s1.acct.grp c.type_cd.val c.cat_cd.val)
    (hr0 : rate.val = 0) (i' : Std.Usize) (hi' : i'.val = i.val + 1) :
    InvS cats accounts acctOf rateOf (rw1, tx, false, last1, total1, acct1, i') ∧
      cats.val.length - i'.val < cats.val.length - i.val := by
  have hlt := hm.lt
  have hR : rRate rateOf s1 (RCat.ofRust c) = s1 := by
    simp [rRate, RCat.ofRust, ← hrate, hr0]
  refine ⟨⟨s1, ?_⟩, by omega⟩
  simp only [Inv]
  refine ⟨hm.rw, hm.tx, hm.first.symm, hm.last, hm.total, by omega, by have := hm.rwl; omega,
    by have := hm.txl; omega, hm.tb, fun _ => ⟨hm.acct, hm.sacct, hm.lastc⟩, ?_⟩
  have hf := hm.fold
  rw [hR] at hf
  rw [hi']; exact hf

/-- The end of an iteration with a nonzero rate (the values as Aeneas' `step*` leaves them). -/
theorem inv_rate_nz (hm : Mid cats accounts acctOf rateOf c i s1 rw1 tx last1 total1 acct1)
    (rate : Std.I64) (hrate : rate.val = rateOf s1.acct.grp c.type_cd.val c.cat_cd.val)
    (hr0 : rate.val ≠ 0) (x4 x3 x2 x1 total' : Std.I64) (tx' : Std.U32) (i' : Std.Usize)
    (h4 : x4.val = c.bal.val * rate.val) (h3 : x3.val = x4.val.tdiv 120000)
    (h2 : x2.val = x3.val.tmod 100000000000) (h1 : x1.val = total1.val + x2.val)
    (h0 : total'.val = x1.val.tmod 100000000000) (htx' : tx'.val = tx.val + 1)
    (hi' : i'.val = i.val + 1) :
    InvS cats accounts acctOf rateOf (rw1, tx', false, last1, total', acct1, i') ∧
      cats.val.length - i'.val < cats.val.length - i.val := by
  have hlt := hm.lt
  have hR : rRate rateOf s1 (RCat.ofRust c) =
      { s1 with total := (s1.total + ((c.bal.val * rate.val).tdiv 120000).tmod 100000000000).tmod
                    100000000000,
                tx := s1.tx + 1 } := by
    simp [rRate, RCat.ofRust, ← hrate, hr0]
  have ht : total'.val =
      (s1.total + ((c.bal.val * rate.val).tdiv 120000).tmod 100000000000).tmod 100000000000 := by
    rw [h0, h1, h2, h3, h4, hm.total]
  have hf := hm.fold
  rw [hR] at hf
  refine ⟨⟨{ s1 with
      total := (s1.total + ((c.bal.val * rate.val).tdiv 120000).tmod 100000000000).tmod 100000000000,
      tx := s1.tx + 1 }, ?_⟩, by omega⟩
  simp only [Inv]
  refine ⟨hm.rw, by rw [htx', hm.tx], hm.first.symm, hm.last, ht, by omega,
    by have := hm.rwl; omega, by have := hm.txl; omega, by rw [← ht]; exact h0 ▸ tmod_bound11 _,
    fun _ => ⟨hm.acct, hm.sacct, hm.lastc⟩, ?_⟩
  rw [hi']; exact hf

end

theorem body_spec (cats : Slice Cat) (accounts : Slice Account) (discs : Slice Disc)
    (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)
    (h : RunPre cats accounts discs acctOf rateOf) (rw : alloc.vec.Vec Account) (tx : Std.U32)
    (first : Bool) (last total : Std.I64) (acct : Option Account) (i : Std.Usize) (m : RState)
    (hinv : Inv cats accounts acctOf rateOf rw tx first last total acct i m) :
    run_loop.body cats accounts discs rw tx first last total acct i ⦃ r =>
      match r with
      | .done y => RunPost cats acctOf rateOf y
      | .cont s => InvS cats accounts acctOf rateOf s ∧
          cats.val.length - s.2.2.2.2.2.2.val < cats.val.length - i.val ⦄ := by
  obtain ⟨hrw, htx, hfirst, hlast, htotal, hi, hrwl, htxl, htb, hacct, hfold⟩ := hinv
  unfold run_loop.body
  by_cases hlt : i.val < cats.val.length
  · -- one record `c`
    have hlt' : i < Slice.len cats := by scalar_tac
    have hcmem : cats.val[i.val] ∈ cats.val := List.getElem_mem hlt
    generalize hc : cats.val[i.val] = c at hcmem
    obtain ⟨hcb, hcex, hcall, hcab, hdex, hdall, hrb⟩ := h.2 c hcmem
    obtain ⟨a, hfa, hav⟩ := acct_found hcex hcall
    have hgrp : (acctOf c.acct_id.val).grp = a.group_id.val := by rw [← hav]; rfl
    obtain ⟨d, hfd, hdv⟩ := disc_found (g := a.group_id) (t := c.type_cd) (k := c.cat_cd)
      (rate := rateOf (acctOf c.acct_id.val).grp c.type_cd.val c.cat_cd.val)
      (by rw [← hgrp]; exact hdex) (by rw [← hgrp]; exact hdall)
    have hdrop : cats.val.drop i.val = c :: cats.val.drop (i.val + 1) := by
      rw [← hc]; exact List.drop_eq_getElem_cons hlt
    rw [hdrop, List.map_cons, List.foldl_cons] at hfold
    simp only [hlt', ↓reduceIte, index_usize_eq' cats i hlt hc, bind_ok]
    cases first
    · -- after the first record: the current account `a0` was read for `last`
      have hf' : m.first = false := hfirst.symm
      obtain ⟨hacc, hmacct, c', hc'mem, hc'id⟩ := hacct rfl
      obtain ⟨-, hcex', hcall', hcab', -, -, -⟩ := h.2 c' hc'mem
      obtain ⟨a0, hfa0, hav0⟩ := acct_found hcex' hcall'
      rw [hc'id] at hfa0 hav0 hcab'
      have hr : d.rate.val.natAbs < 1000000 := hdv ▸ hrb
      have hprod : (c.bal.val * d.rate.val).natAbs < 100000000000000000 := by
        rw [Int.natAbs_mul]
        exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hcb hr) (by decide)
      have hp1 : I64.min ≤ c.bal.val * d.rate.val := by rw [I64.min_eq]; omega
      have hp2 : c.bal.val * d.rate.val ≤ I64.max := by rw [I64.max_eq]; omega
      by_cases hsame : c.acct_id = last
      · -- the same account: no change
        have hne : (c.acct_id != last) = false := by simp [hsame]
        have hacct_a : acct = some a := by rw [hacc, ← hsame, hfa]
        simp only [Bool.false_eq_true, ↓reduceIte, hne, bind_ok, Aeneas.Std.uncurry_apply_pair,
          hacct_a, expect_some, read_rate_eq _ _ _ _ d hfd, bind_ite]
        have hm : Mid cats accounts acctOf rateOf c i m rw tx last total (some a) :=
          { rw := hrw, tx := htx, first := hf', last := hlast, total := htotal, lt := hlt,
            rwl := by omega, txl := htxl, tb := htb, acct := hacct_a ▸ hacc, sacct := hmacct,
            lastc := ⟨c', hc'mem, hc'id⟩,
            fold := by
              rw [rStep_same acctOf rateOf m (RCat.ofRust c) hf'
                (by simp [RCat.ofRust, hsame, hlast])] at hfold
              exact hfold }
        have hrate : d.rate.val = rateOf m.acct.grp c.type_cd.val c.cat_cd.val := by
          rw [hmacct, ← hsame]; exact hdv
        step*
        · -- `total + monthly` within `i64`
          have hx : x.val.natAbs < 100000000000 := by rw [x_post]; exact tmod_bound11 _
          rw [I64.min_eq]; omega
        · have hx : x.val.natAbs < 100000000000 := by rw [x_post]; exact tmod_bound11 _
          rw [I64.max_eq]; omega
        · rename_i hne x4 _ h4 x3 _ h3 x2 _ h2 x1 _ h1 x0 _ h0 _
          exact inv_rate_nz hm d.rate hrate (by simpa [IScalar.eq_equiv] using hne) x4 x3 x2 x1 x0
            x i2 h4 h3 h2 h1 h0 x_post i2_post
        · rename_i hz
          exact inv_rate_zero hm d.rate hrate (by simpa [IScalar.eq_equiv] using hz) i2 i2_post
      · -- an account change: post the interest of `a0`
        have hne : (c.acct_id != last) = true := by simp [hsame]
        have hacct0 : acct = some a0 := hacc.trans hfa0
        have hb0 : a0.bal.val.natAbs < 1000000000000 := by
          have : a0.bal.val = (acctOf last.val).bal := by rw [← hav0]; rfl
          rw [this]; exact hcab'
        obtain ⟨a1, hpost, ha1⟩ := post_eq a0 total hb0 (by rw [htotal]; exact htb)
        have hlen : rw.val.length < Usize.max := by
          have h1 := congrArg List.length hrw
          have h2 := cats.property
          simp only [List.length_map] at h1
          omega
        obtain ⟨rw3, hpush, hrw3⟩ := push_eq rw a1 hlen
        simp only [Bool.false_eq_true, ↓reduceIte, hne, bind_ok, Aeneas.Std.uncurry_apply_pair,
          hacct0, unwrap_some, hpost, hpush, read_account_eq, hfa, expect_some,
          read_rate_eq _ _ _ _ d hfd, bind_ite]
        have hm : Mid cats accounts acctOf rateOf c i
            ⟨m.rewrites ++ [rPost m.acct m.total], m.tx, false, c.acct_id.val, 0,
              acctOf c.acct_id.val⟩ rw3 tx c.acct_id 0#i64 (some a) :=
          { rw := by rw [hrw3, List.map_append, hrw, List.map_singleton, ha1, hav0, hmacct, htotal]
            tx := htx, first := rfl, last := rfl, total := by simp, lt := hlt,
            rwl := by simp; omega, txl := htxl, tb := by simp, acct := hfa.symm, sacct := rfl,
            lastc := ⟨c, hcmem, rfl⟩,
            fold := by
              have hc2 : (RCat.ofRust c).acct ≠ m.last := by
                simp only [RCat.ofRust, ← hlast]
                intro he; exact hsame (IScalar.eq_of_val_eq he)
              rw [rStep_change acctOf rateOf m (RCat.ofRust c) hf' hc2] at hfold
              exact hfold }
        step*
        · rename_i hne x4 _ h4 x3 _ h3 x2 _ h2 x1 _ h1 x0 _ h0 _
          exact inv_rate_nz hm d.rate hdv (by simpa [IScalar.eq_equiv] using hne) x4 x3 x2 x1 x0
            x i2 h4 h3 h2 (by rw [h1]; simp) h0 x_post i2_post
        · rename_i hz
          exact inv_rate_zero hm d.rate hdv (by simpa [IScalar.eq_equiv] using hz) i2 i2_post
    · -- the first record
      simp only [↓reduceIte, read_account_eq, hfa, bind_ok, Aeneas.Std.uncurry_apply_pair,
        expect_some, read_rate_eq _ _ _ _ d hfd, bind_ite]
      have hm : Mid cats accounts acctOf rateOf c i
          ⟨m.rewrites, m.tx, false, c.acct_id.val, 0, acctOf c.acct_id.val⟩ rw tx c.acct_id 0#i64
          (some a) :=
        { rw := hrw, tx := htx, first := rfl, last := rfl, total := by simp, lt := hlt,
          rwl := by simp; omega, txl := htxl, tb := by simp, acct := hfa.symm, sacct := rfl,
          lastc := ⟨c, hcmem, rfl⟩,
          fold := by
            rw [rStep_first acctOf rateOf m (RCat.ofRust c) hfirst.symm] at hfold
            exact hfold }
      have hr : d.rate.val.natAbs < 1000000 := hdv ▸ hrb
      have hprod : (c.bal.val * d.rate.val).natAbs < 100000000000000000 := by
        rw [Int.natAbs_mul]
        exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hcb hr) (by decide)
      have hp1 : I64.min ≤ c.bal.val * d.rate.val := by rw [I64.min_eq]; omega
      have hp2 : c.bal.val * d.rate.val ≤ I64.max := by rw [I64.max_eq]; omega
      step*
      · rename_i hne x4 _ h4 x3 _ h3 x2 _ h2 x1 _ h1 x0 _ h0 _
        exact inv_rate_nz hm d.rate hdv (by simpa [IScalar.eq_equiv] using hne) x4 x3 x2 x1 x0 x i2
          h4 h3 h2 (by rw [h1]; simp) h0 x_post i2_post
      · rename_i hz
        exact inv_rate_zero hm d.rate hdv (by simpa [IScalar.eq_equiv] using hz) i2 i2_post
  · -- end of the records: the fold is complete
    have hlt' : ¬ (i < Slice.len cats) := by scalar_tac
    simp only [hlt', ↓reduceIte, WP.spec_ok]
    have hieq : i.val = cats.val.length := by omega
    rw [hieq, List.drop_eq_nil_of_le (le_refl _), List.map_nil, List.foldl_nil] at hfold
    rw [RunPost, ← hfold]
    exact ⟨hrw, htx⟩

/-- **The Rust `run` on inputs satisfying `RunPre`** (Aeneas specification: it returns `ok`,
no panic): the rewrites and the transaction count of `rRun`. -/
theorem run_spec (cats : Slice Cat) (accounts : Slice Account) (discs : Slice Disc)
    (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)
    (h : RunPre cats accounts discs acctOf rateOf) :
    run cats accounts discs ⦃ r => RunPost cats acctOf rateOf r ⦄ := by
  unfold run run_loop
  apply loop.spec_decr_nat (fun s => cats.val.length - s.2.2.2.2.2.2.val)
    (InvS cats accounts acctOf rateOf)
  · rintro ⟨rw, tx, first, last, total, acct, i⟩ ⟨m, hinv⟩
    dsimp only
    refine WP.spec_mono
      (body_spec cats accounts discs acctOf rateOf h rw tx first last total acct i m hinv) ?_
    rintro (s | y) hr <;> exact hr
  · refine ⟨rInit, ?_⟩
    simp [Inv, rInit, rRun]

/-- **The Rust `run` returns `ok`** (no panic) **with exactly the rewrites and the count of the
fold `rRun`**, on every input satisfying `RunPre`. -/
theorem run_eq (cats : Slice Cat) (accounts : Slice Account) (discs : Slice Disc)
    (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)
    (h : RunPre cats accounts discs acctOf rateOf) :
    ∃ rw n, run cats accounts discs = ok (rw, n) ∧
      rw.val.map RAcct.ofRust = (rRun acctOf rateOf (cats.val.map RCat.ofRust)).rewrites ∧
      n.val = (rRun acctOf rateOf (cats.val.map RCat.ofRust)).tx := by
  obtain ⟨⟨rw, n⟩, hr, hp⟩ := (spec_iff_exists _ _).1 (run_spec cats accounts discs acctOf rateOf h)
  exact ⟨rw, n, hr, hp⟩

end EquivLean.Demo.Cbact04cRust

#print axioms EquivLean.Demo.Cbact04cRust.run_spec
#print axioms EquivLean.Demo.Cbact04cRust.run_eq
