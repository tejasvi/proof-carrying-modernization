import EquivLean.Demo.Cobol.Cbact04cRust.Arith
import EquivLean.Demo.Cobol.Cbact04cRust.Model

/-!
# The Rust loop on CBACT04C's inputs computes coblean's specification

`rRun` (the main loop of `cbact04c::run` on integers, `Cbact04cRust/Model.lean`) on the category records of
the accounts `accs`, grouped by account as in the COBOL input file, rewrites every account but
the last with its posted interest (`Acc.posted (totalInt …)` of coblean's `cbact04c_all`, as Rust
values) and counts the transactions `nTxA`.  Pure list induction, as `jRun_cbact04c` for the Java
loop (`Demo/Jimple/Cbact04c/Pure.lean`), with the arithmetic of `Cbact04cRust/Arith.lean`; on integers the
steps need no bounds.
-/

open Cobol CardDemo.Cbact04c

namespace EquivLean.Demo.Cbact04cRust

/-- The big-endian value of a list of bytes: an alphanumeric key as a Rust integer (`u16` for the
type code, `u128` for the group id). -/
def beNat (bs : List UInt8) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- A category record of the account `a`, as the Rust values hold it. -/
def rcat (a : Acc) (c : Cat) : RCat := ⟨a.id, beNat c.ty, c.cat, c.bal⟩

/-- An account record, as the Rust values hold it. -/
def racct (a : Acc) : RAcct := ⟨a.id, a.bal, a.cc, a.cd, beNat a.grp⟩

/-- The category records in file order, as Rust values. -/
def rcats (accs : List Acc) : List RCat := (items accs).map fun p => rcat p.1 p.2

/-- coblean's rewritten account record `a.posted t`, as the values of a Rust account. -/
def rposted (a : Acc) (t : Int) : RAcct :=
  ⟨a.id, (Sem.fitNum {} ACCT_CURR_BAL.fmt (a.bal + t)).2, 0, 0, beNat a.grp⟩

/-- The loop state after the accounts `pre` and the first categories `dc` of the account `cur`. -/
def RS (rate : Acc → Cat → Int) (pre : List Acc) (cur : Acc) (dc : List Cat) : RState :=
  ⟨pre.map (fun a => rposted a (totalInt (rate a) a.cats)),
   nTxA rate (items pre ++ dc.map (Prod.mk cur)), false, cur.id, totalInt (rate cur) dc, racct cur⟩

section
variable (rate : Acc → Cat → Int) (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)

theorem totalInt_concat (r : Cat → Int) (dc : List Cat) (c : Cat) :
    totalInt r (dc ++ [c]) = addInt r (totalInt r dc) c := by
  simp [totalInt, List.foldl_append]

theorem nTxA_concat (done : List (Acc × Cat)) (p : Acc × Cat) :
    nTxA rate (done ++ [p]) = nTxA rate done + (if rate p.1 p.2 ≠ 0 then 1 else 0) := by
  unfold nTxA
  rw [List.filter_append, List.length_append]
  by_cases h : rate p.1 p.2 ≠ 0 <;> simp [h]

/-- The rate step of one category `c` of the current account `cur`. -/
theorem rate_step (pre : List Acc) (cur : Acc) (dc : List Cat) (c : Cat)
    (hro : rateOf (beNat cur.grp) (beNat c.ty) c.cat = rate cur c) :
    rRate rateOf (RS rate pre cur dc) (rcat cur c) = RS rate pre cur (dc ++ [c]) := by
  simp only [rRate, RS, rcat, racct, hro]
  by_cases h0 : rate cur c = 0
  · simp only [h0, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
      nTxA_concat, ne_eq, not_true_eq_false, totalInt_concat, addInt, Nat.add_zero]
  · simp only [h0, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
      nTxA_concat, ne_eq, not_false_eq_true, totalInt_concat, addInt, rtotal_step]

/-- A record of the current account: no account change. -/
theorem chg_same (pre : List Acc) (cur : Acc) (dc : List Cat) (c : Cat) :
    rChg acctOf (RS rate pre cur dc) (rcat cur c) = RS rate pre cur dc := by
  simp [rChg, RS, rcat]

/-- The first record of the next account `nxt`: `cur` is posted. -/
theorem chg_next (pre : List Acc) (cur nxt : Acc) (c : Cat) (hne : nxt.id ≠ cur.id)
    (hacct : acctOf nxt.id = racct nxt) :
    rChg acctOf (RS rate pre cur cur.cats) (rcat nxt c) = RS rate (pre ++ [cur]) nxt [] := by
  have hpost : rPost (racct cur) (totalInt (rate cur) cur.cats) =
      rposted cur (totalInt (rate cur) cur.cats) := by
    simp only [rPost, racct, rposted, rpost_bal]
  simp only [rChg, RS, rcat, Bool.false_or, bne_iff_ne, ne_eq, hne, not_false_eq_true,
    ↓reduceIte, Bool.false_eq_true, hacct, hpost, List.map_append, List.map_cons,
    List.map_nil, items_concat, List.append_nil]
  simp [totalInt]

/-- The first record of the file. -/
theorem chg_first (a : Acc) (c : Cat) (hacct : acctOf a.id = racct a) :
    rChg acctOf rInit (rcat a c) = RS rate [] a [] := by
  simp [rChg, rInit, RS, rcat, hacct, items, nTxA, totalInt]

/-- The records of the current account. -/
theorem fold_cats (pre : List Acc) (cur : Acc) :
    ∀ (cs dc : List Cat), (∀ c ∈ cs, rateOf (beNat cur.grp) (beNat c.ty) c.cat = rate cur c) →
    (cs.map (rcat cur)).foldl (rStep acctOf rateOf) (RS rate pre cur dc) = RS rate pre cur (dc ++ cs)
  | [], dc, _ => by simp
  | c :: cs, dc, h => by
    rw [List.map_cons, List.foldl_cons, rStep_eq, chg_same,
      rate_step rate rateOf pre cur dc c (h c (List.mem_cons_self ..)),
      fold_cats pre cur cs (dc ++ [c]) (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp

/-- What every account of the input satisfies: it has a category record, its account record is
found (`acctOf`), and so are its rates (`rateOf`, keyed by the integer values of the group id and
the type code). -/
def AccOk (a : Acc) : Prop :=
  a.cats ≠ [] ∧ acctOf a.id = racct a ∧
    ∀ c ∈ a.cats, rateOf (beNat a.grp) (beNat c.ty) c.cat = rate a c

theorem rcats_cons (a : Acc) (rest : List Acc) :
    rcats (a :: rest) = a.cats.map (rcat a) ++ rcats rest := by
  simp [rcats, items, List.map_flatMap, Function.comp_def]

/-- The accounts after the current one. -/
theorem fold_accounts : ∀ (rest pre : List Acc) (cur : Acc),
    (∀ a ∈ cur :: rest, AccOk rate acctOf rateOf a) →
    (cur :: rest).Pairwise (fun a b => a.id ≠ b.id) →
    (rcats rest).foldl (rStep acctOf rateOf) (RS rate pre cur cur.cats) =
      RS rate (pre ++ (cur :: rest).dropLast) ((cur :: rest).getLast (List.cons_ne_nil _ _))
        ((cur :: rest).getLast (List.cons_ne_nil _ _)).cats
  | [], pre, cur, _, _ => by simp [rcats, items]
  | nxt :: rest, pre, cur, hok, hd => by
    have hnxt := hok nxt (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hne : nxt.id ≠ cur.id := fun h =>
      (List.rel_of_pairwise_cons hd (List.mem_cons_self ..)) h.symm
    obtain ⟨c0, cs, hcs⟩ : ∃ c0 cs, nxt.cats = c0 :: cs := by
      cases h : nxt.cats with
      | nil => exact absurd h hnxt.1
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    rw [rcats_cons, List.foldl_append, hcs, List.map_cons, List.foldl_cons, rStep_eq,
      chg_next rate acctOf pre cur nxt c0 hne hnxt.2.1,
      rate_step rate rateOf (pre ++ [cur]) nxt [] c0
        (hnxt.2.2 c0 (by rw [hcs]; exact List.mem_cons_self ..)), List.nil_append,
      fold_cats rate acctOf rateOf (pre ++ [cur]) nxt cs [c0] (fun c hc =>
        hnxt.2.2 c (by rw [hcs]; exact List.mem_cons_of_mem _ hc))]
    have hrest := fold_accounts rest (pre ++ [cur]) nxt (fun a ha => hok a (List.mem_cons_of_mem _ ha))
      (List.Pairwise.of_cons hd)
    rw [show [c0] ++ cs = nxt.cats by rw [hcs]; rfl, hrest]
    simp [List.dropLast_cons_cons, List.getLast_cons]

end

/-- **The Rust loop on CBACT04C's input** (records of the accounts `accs` in file order, each
account's record and rates found): the rewrites are coblean's `a.posted (totalInt …)` for every
account but the last (as Rust values), and the transaction count is `nTxA`. -/
theorem rRun_cbact04c (rate : Acc → Cat → Int) (acctOf : Int → RAcct)
    (rateOf : Nat → Nat → Int → Int) (accs : List Acc)
    (hok : ∀ a ∈ accs, AccOk rate acctOf rateOf a)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) :
    (rRun acctOf rateOf (rcats accs)).rewrites =
        accs.dropLast.map (fun a => rposted a (totalInt (rate a) a.cats)) ∧
      (rRun acctOf rateOf (rcats accs)).tx = nTxA rate (items accs) := by
  cases accs with
  | nil => simp [rRun, rcats, items, rInit, nTxA]
  | cons a rest =>
    have ha := hok a (List.mem_cons_self ..)
    obtain ⟨c0, cs, hcs⟩ : ∃ c0 cs, a.cats = c0 :: cs := by
      cases h : a.cats with
      | nil => exact absurd h ha.1
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    simp only [rRun]
    rw [rcats_cons, List.foldl_append, hcs, List.map_cons, List.foldl_cons, rStep_eq,
      chg_first rate acctOf a c0 ha.2.1,
      rate_step rate rateOf [] a [] c0 (ha.2.2 c0 (by rw [hcs]; exact List.mem_cons_self ..)),
      List.nil_append, fold_cats rate acctOf rateOf [] a cs [c0] (fun c hc =>
        ha.2.2 c (by rw [hcs]; exact List.mem_cons_of_mem _ hc)),
      show [c0] ++ cs = a.cats by rw [hcs]; rfl,
      fold_accounts rate acctOf rateOf rest [] a hok hdist]
    refine ⟨by simp [RS], ?_⟩
    simp only [RS, List.nil_append]
    rw [← items_concat, List.dropLast_concat_getLast]

end EquivLean.Demo.Cbact04cRust

#print axioms EquivLean.Demo.Cbact04cRust.rRun_cbact04c
